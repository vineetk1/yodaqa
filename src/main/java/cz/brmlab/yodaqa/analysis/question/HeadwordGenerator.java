package cz.brmlab.yodaqa.analysis.question;

import de.tudarmstadt.ukp.dkpro.core.api.lexmorph.type.pos.ADV;
import de.tudarmstadt.ukp.dkpro.core.api.segmentation.type.Token;
import de.tudarmstadt.ukp.dkpro.core.api.segmentation.type.Split;
import de.tudarmstadt.ukp.dkpro.core.api.syntax.type.constituent.Constituent;
import de.tudarmstadt.ukp.dkpro.core.api.syntax.type.constituent.ROOT;
import de.tudarmstadt.ukp.dkpro.core.api.lexmorph.type.pos.POS;
import de.tudarmstadt.ukp.dkpro.core.api.syntax.type.dependency.Dependency;
import de.tudarmstadt.ukp.dkpro.core.api.syntax.type.dependency.ADVMOD;
import de.tudarmstadt.ukp.dkpro.core.api.syntax.type.dependency.DEP;
import de.tudarmstadt.ukp.dkpro.core.api.syntax.type.dependency.DET;
import de.tudarmstadt.ukp.dkpro.core.api.syntax.type.dependency.DOBJ;
import de.tudarmstadt.ukp.dkpro.core.api.syntax.type.dependency.NSUBJ;

import org.apache.uima.UimaContext;
import org.apache.uima.analysis_engine.AnalysisEngineProcessException;
import org.apache.uima.fit.component.JCasAnnotator_ImplBase;
import org.apache.uima.fit.util.JCasUtil;
import org.apache.uima.cas.FeatureStructure;
import org.apache.uima.jcas.cas.FSArray;
import org.apache.uima.jcas.JCas;
import org.apache.uima.jcas.tcas.Annotation;
import org.apache.uima.resource.ResourceInitializationException;

import java.util.Hashtable;
import java.util.List;
import java.util.Arrays;
import java.lang.String;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import cz.brmlab.yodaqa.model.Question.Headword;
import cz.brmlab.yodaqa.model.Question.Focus;

//import cz.brmlab.yodaqa.model.Question.QuestionInfo;

/*
 * Author: Vineet Kumar, Sioom Corporation
 *
 * The HeadwordGenerator class is an implementation of "Silva, J. P. C. G. (2009). QA+ML@ Wikipedia&Google 
 * (Doctoral dissertation, Instituto Superior Técnico)" and 
 * "Loni, B. (2011). Enhanced question classification with optimal combination of features 
 * (Master's thesis, Delft University of Technology)", plus 
 * major additions and modifications are made based on research done at Sioom Corporation 
 *
 * The headword is one single word specifying the object that the question seeks. Following examples 
 * show the headword in brackets: 
 * What is a group of [turkeys] called?
 * George Bush purchased a small interest in which baseball [team]?
 *
 * The HeadwordGenerator class traverses the parse tree of the question to find the headword. 
 * Major methods are as follows:
 * (1) questionHasRuleBasedHeadword() filters out those questions that do not require Rules to find
 *     headwords
 * (2) findRuleBasedHeadword() is the main method that calls most other methods in this class
 * (3) applyRules() has rules to find the next head node in the tree, finally leading to the headword 
 * (4) applyNonTrivialRules() has rules that cover those cases where applyRules() do not work
 * (5) postOperationFix() finds a new path in the tree if a head node is a type-word
 */

public class HeadwordGenerator extends JCasAnnotator_ImplBase {
	final Logger logger = LoggerFactory.getLogger(HeadwordGenerator.class);

	private Hashtable<String, List<String>> priorityListTable;
	private Hashtable<String, searchDirection> directionTable;
	private List<String> typeWords;

	private enum searchDirection
	{
		LeftByCategory, RightByCategory, LeftByPosition, RightByPosition
	}

	private void makeHeadRules()
	{
		priorityListTable = new Hashtable<String, List<String>>();
		directionTable = new Hashtable<String, searchDirection>();
		
		priorityListTable.put("S", Arrays.asList("VP", "S", "FRAG", "SBAR", "ADJP"));
		priorityListTable.put("SBARQ", Arrays.asList("SQ", "S", "SINV", "SBARQ", "FRAG"));
		priorityListTable.put("SQ", Arrays.asList("NP", "VP", "SQ"));
		priorityListTable.put("NP", Arrays.asList("NP", "NN", "NNP", "NNPS", "NNS", "NX"));
		priorityListTable.put("PP", Arrays.asList("WHNP","NP", "WHADVP", "SBAR"));
		priorityListTable.put("WHNP", Arrays.asList("NP", "NN", "NNP", "NNPS", "NNS", "NX", "WHNP")); 
		priorityListTable.put("WHADVP", Arrays.asList("NP", "NN", "NNP", "NNPS", "NNS", "NX", "WHNP"));
		priorityListTable.put("WHADJP", Arrays.asList("NP", "NN", "NNP", "NNPS", "NNS", "NX", "WHNP"));
		priorityListTable.put("WHPP", Arrays.asList("WHNP", "WHADVP", "NP", "SBAR"));
		priorityListTable.put("ROOT", Arrays.asList("S", "SBARQ"));
		priorityListTable.put("VP", Arrays.asList("NP", "NN", "NNP", "NNPS", "NNS", "NX", "SQ", "PP"));
		priorityListTable.put("SINV", Arrays.asList("NP"));
		priorityListTable.put("NX", Arrays.asList("NP", "NN", "NNP", "NNPS", "NNS", "NX", "S"));
		
		directionTable.put("S", searchDirection.LeftByCategory);
		directionTable.put("SBARQ", searchDirection.LeftByCategory);
		directionTable.put("SQ", searchDirection.LeftByCategory);
		directionTable.put("NP", searchDirection.RightByPosition);
		directionTable.put("PP", searchDirection.LeftByCategory);
		directionTable.put("WHNP", searchDirection.LeftByCategory);
		directionTable.put("WHPP", searchDirection.RightByCategory);
		directionTable.put("WHADVP", searchDirection.LeftByCategory);
		directionTable.put("WHADJP", searchDirection.LeftByCategory);
		directionTable.put("ROOT", searchDirection.LeftByCategory);
		directionTable.put("VP", searchDirection.RightByCategory);
		directionTable.put("SINV", searchDirection.LeftByCategory);
		directionTable.put("NX", searchDirection.LeftByCategory);
		
		typeWords = Arrays.asList("kind", "name", "type", "part", "genre", "group");

	}

private static int count = 0;
	public void initialize(UimaContext aContext) throws ResourceInitializationException {
		super.initialize(aContext);
		makeHeadRules();
	}

	public void process(JCas jcas) throws AnalysisEngineProcessException {

String qText = null;

		for (ROOT rootNode : JCasUtil.select(jcas, ROOT.class)) {
//dumpCTree(rootNode, 0);
			if (questionHasRuleBasedHeadword(jcas, rootNode)) 	
				findRuleBasedHeadword(jcas, rootNode); 
qText = ((Constituent)rootNode).getCoveredText();			
		}

String focusText = null;
String headwordText = null;

		for (Focus focus : JCasUtil.select(jcas, Focus.class)) {
			focusText = focus.getToken().getCoveredText();
		}
		for (Headword headword : JCasUtil.select(jcas, Headword.class)) {
			headwordText = headword.getBase().getCoveredText();
		}
		if ( focusText == null && headwordText == null) {
System.out.println("#@" + ++count + " Question: " + qText);
System.out.println("#@" + count + " Both focus and headword are null ");
		} else if ((focusText == null && headwordText != null) 
			|| (focusText != null && headwordText == null)
			|| (!focusText.equalsIgnoreCase(headwordText))) {
System.out.println("#@" + ++count + " Question: " + qText);
System.out.println("#@" + count + " focus: " + focusText + " != headword: " + headwordText);
		}
	}


	private boolean questionHasRuleBasedHeadword(JCas jcas, Constituent rootNode) {

		/* (1) Question text of certain wh-words do not have a headword. The headword is implicit 
		 * in those wh-words as follows: when => time, date; where => location, organization; 
		 * who/whom => person; why => reason.
		 * (2) how => description, except when the word following "who" is a headword if it is
		 * an adjective or an adverb
		 * (3) Question with 1 or 2 words => meaning/definition
		 */ 

		boolean nextWordAfterHow = false;
		int numberOfTokens = 0;
		Token howToken = null;

		for (Token token : JCasUtil.selectCovered(Token.class, rootNode)) {
			numberOfTokens++;
			String qWord = token.getCoveredText().toLowerCase();

			if (nextWordAfterHow) {
				String pos = token.getPos().getPosValue().toLowerCase();
				if (pos.equals("jj") || pos.equals("rb")) {
					logger.debug("Headword: {} {}", token.getPos().getPosValue(), 
						token.getCoveredText());
					writeHeadword (jcas, token);
				} else {
					logger.debug("Headword: {} {}", howToken.getPos().getPosValue(), 
						howToken.getCoveredText());
					writeHeadword (jcas, howToken);
				}
				return false;
			} else if (qWord.startsWith("wh")) {
				switch (qWord) {
					case "when": case "where": case "who": case "whom": case "why":
						logger.debug("Headword: {}", token.getCoveredText()); 
						writeHeadword (jcas, token);
						return false;
					case "what": case "which": 
						/* Question Patterns (see Silva's dissertation) are not 
						 * implemented; they should be implemented
						 */ 
						return true;
					default:
				} 
			} else if (qWord.equals("how")) {
				howToken = token;
				nextWordAfterHow = true;
			}
		}

		if (numberOfTokens <= 2) {
			logger.debug("No headword, question has less than or equal to two tokens: {}",
					((Constituent)rootNode).getCoveredText());			
System.out.println("# questionHasRuleBasedHeadword: no headword, question is less than equal to two tokens");
			return false; 
		}

System.out.println("# questionHasRuleBasedHeadword: no wh or how found");
		return true;
	}



	private void findRuleBasedHeadword(JCas jcas, Constituent node) {
		assert node.getConstituentType().equals("ROOT") : node.getConstituentType(); 

		while (true) {
System.out.println("# findRuleBasedHeadword: start with node c " +  node.getConstituentType()  + " " + node.getSyntacticFunction() + " [" + node.getCoveredText() + "]");
			FeatureStructure headNode;

			{
				Constituent adjustedNode = applyNonTrivialRules(node);
				if (!adjustedNode.equals(node)) {
					node = adjustedNode;
System.out.println("# findRuleBasedHeadword: nonTrivialRules adjust c " +  node.getConstituentType()  + " " + node.getSyntacticFunction() + " [" + node.getCoveredText() + "]");
					continue;
				}
			}

			try {
				headNode = applyRules(node);
			} catch (Exception e) {
System.out.println("# findRuleBasedHeadword: Exception occured, no headword ");
				logger.debug("Caught Exception, No headword: {}", e.getMessage());
				// e.printStackTrace();
				return;
			}

			if (headNode instanceof Token) {
System.out.println("# findRuleBasedHeadword:found t " + ((Token) headNode).getPos().getPosValue() + " " + ((Token) headNode).getLemma().getValue() + " [" + ((Token) headNode).getCoveredText() + "]");
				if (typeWords.contains(((Token) headNode).getLemma().getValue())) { 
					FeatureStructure postFixNode = postOperationFix((Token) headNode);
					if ((postFixNode == null) || (postFixNode instanceof Token)) {
						if ((postFixNode instanceof Token) && (postFixNode != null)) {
							headNode = postFixNode;
System.out.println("# findRuleBasedHeadword:postFix t " + ((Token) headNode).getPos().getPosValue() + " " + ((Token) headNode).getLemma().getValue() + " [" + ((Token) headNode).getCoveredText() + "]");
						}
					} else if (postFixNode instanceof Constituent) {
						node = (Constituent) postFixNode;
System.out.println("# findRuleBasedHeadword: postFix c " +  node.getConstituentType()  + " " + node.getSyntacticFunction() + " [" + node.getCoveredText() + "]");
						continue;
					} else 
						throw new AssertionError("neither token nor constituent");
				}
				logger.debug("Headword: {}", ((Token) headNode).getCoveredText());
				writeHeadword(jcas, (Token) headNode); 
				return;
			} else if (headNode instanceof Constituent) {
				node = (Constituent) headNode;
				continue;
			} else 
				throw new AssertionError("neither token nor constituent");
		}
	}


		

	private Constituent applyNonTrivialRules(Constituent parentNode) {
		assert parentNode.getChildren().size() > 0 : "no child nodes of "+ parentNode;
		
		String parentNodePOS = parentNode.getConstituentType();
		assert parentNodePOS != null : "null parentNodePOS of " + parentNodePOS;	
		
		/* Rule 1: if SBARQ has WH*P child with at least two children, return WH*P; Without
		 * this rule, applyRules() returns an incorrect headword of [chocolates] from the
		 * question: Which [country] are Godiva chocolates from?
		 */
		if (parentNodePOS.equals("SBARQ"))
			for (FeatureStructure childNode : parentNode.getChildren().toArray()) {
				assert ((childNode instanceof Token) || (childNode instanceof Constituent)) :
					"child node is neither token nor constituent";
				if (childNode instanceof Constituent) 
					if ((((Constituent) childNode).getConstituentType().startsWith("WH"))
					&& (((Constituent) childNode).getConstituentType().endsWith("P"))
					&& (((Constituent) childNode).getChildren().size() >= 2))
						return (Constituent) childNode;
			}

		/* Rule 2: if WH** has a`possessive pronoun (POS) token down the tree, return parent
		 * of POS token; Note: this rule is different from that described in Silva;
		 * Without this rule, applyRules() returns an incorrect headword of [capital] from the
		 * question: What [country]'s capital is tirana?
		 */	   
		if (parentNodePOS.startsWith("WH")) {
			Constituent nodeFound = findNodeWithPosOfPOS(parentNode);
			if (nodeFound != null) 
				return nodeFound;
		}

		// non-trivial rules did not apply
		return parentNode;
	}




	private Constituent findNodeWithPosOfPOS(Constituent parentNode) {
		for (FeatureStructure childNode : parentNode.getChildren().toArray()) {
			if (childNode instanceof Token) {
				if (((Token) childNode).getPos().getPosValue().equals("POS")) 
					return parentNode;
			} else if (childNode instanceof Constituent) {
				Constituent nodeFound = findNodeWithPosOfPOS((Constituent) childNode);
				if (nodeFound != null) 
					return nodeFound;
			} else 
				throw new AssertionError("neither token nor constituent");
		}
		return (Constituent) null;
	}
		



	private FeatureStructure applyRules(Constituent parentNode) throws Exception {
		int childNodesArraySize = parentNode.getChildren().size();
		assert childNodesArraySize > 0 : "childNodesArraySize is "+ childNodesArraySize;
		FeatureStructure[] childNodes = parentNode.getChildren().toArray();
		if (childNodesArraySize == 1)
			return childNodes[0];

		String parentNodePOS = parentNode.getConstituentType();
		assert parentNodePOS != null : "parentNodePOS: " + parentNodePOS;
	
		List<String> priorityList = priorityListTable.get(parentNodePOS);
		if (priorityList == null)
			throw new Exception("parentNodePOS does not match any key in priorityListTable; alien parentNodePOS: " + parentNodePOS);

		switch (directionTable.get(parentNodePOS)) {
			case RightByCategory:
				for (String pos : priorityList) 
					for (int i =  childNodesArraySize - 1; i >= 0; i--) 		
						if (match (pos, childNodes[i]))	
							return childNodes[i];
				break;
			case LeftByCategory:
				for (String pos : priorityList) 
					for (FeatureStructure childNode : childNodes) 
						if (match (pos, childNode))	
							return childNode;
				break;
			case RightByPosition:
				for (int i =  childNodesArraySize - 1; i >= 0; i--) 		
					for (String pos : priorityList) 
						if (match (pos, childNodes[i]))	
							return childNodes[i];
				break;
			case LeftByPosition:
				for (FeatureStructure childNode : childNodes) 
					for (String pos : priorityList)
						if (match (pos, childNode))	
							return childNode;
				break;
			default: 
				throw new AssertionError("Not possible to have a non-null priorityList but an alien searchDirection of " +  directionTable.get(parentNodePOS));
		}
		throw new Exception("POS in priority list of " + parentNodePOS + " != POS in child nodes of " + Arrays.toString(childNodes));
	}




	private Boolean match (String pos, FeatureStructure node) {
		boolean matches = false;
		if (node instanceof Token) {
			if (((Token) node).getPos().getPosValue().equals(pos))
				matches = true;
		} else if (node instanceof Constituent) {
			if (((Constituent) node).getConstituentType().equals(pos))
				matches = true;
		} else 
			throw new AssertionError("neither token nor constituent");
		return matches;
	}
	



	private FeatureStructure postOperationFix(Token headNode) {
		/* Rule: if headword is typeWord and a child of some ancestor node is a prepositional 
		 * phrase (PP), return child node as headNode; Note: this rule is different from that 
		 * described in Silva; In the question: What kind of [animal] is Babar?,  
		 * applyRules() returns the headword [kind] but [animal] is a better headword
		 */	   
		Constituent parentNode = (Constituent) (headNode.getParent());
		for (int levelsUpTree = 1; levelsUpTree <= 2; levelsUpTree++) {
			for (FeatureStructure childNode : parentNode.getChildren().toArray()) {
				if (childNode instanceof Token) {
					if (((Token) childNode).getPos().getPosValue().equals("PP")) 
						return childNode;
				} else if (childNode instanceof Constituent) {
					if (((Constituent) childNode).getConstituentType().equals("PP")) 
						return childNode;
				} else 
					throw new AssertionError("neither token nor constituent");
			}
			if ((parentNode.getConstituentType().equals("ROOT"))) 
				break;
			else
				parentNode = (Constituent) (parentNode.getParent());
		}
		return (FeatureStructure) null;
	}




	protected void writeHeadword(JCas jcas, Token headNode) {
		Headword headword = new Headword(jcas);
		headword.setBegin(headNode.getBegin());
		headword.setEnd(headNode.getEnd());
		headword.setBase(headNode);
		headword.addToIndexes();
	}




	// dumpCTree and dumpTLeaf are only for debugging the code of this class; remove when not needed
	private void dumpCTree(Constituent c, int level) {
		for (int i = 0; i < level; i++)
			System.out.print(" ");
		System.out.println("c " + c.getConstituentType() + " " + c.getSyntacticFunction() + " [" + c.getCoveredText() + "]");

		for (FeatureStructure child : c.getChildren().toArray()) {
			if (child instanceof Token) {
				dumpTLeaf((Token) child, level + 1);
				continue;
			}
			dumpCTree((Constituent) child, level + 1);
		}
	}
	private void dumpTLeaf(Token t, int level) {
		for (int i = 0; i < level; i++)
			System.out.print(" ");
		System.out.println("t " + t.getPos().getPosValue() + " " + t.getLemma().getValue() + " [" + t.getCoveredText() + "]");
	}

}
