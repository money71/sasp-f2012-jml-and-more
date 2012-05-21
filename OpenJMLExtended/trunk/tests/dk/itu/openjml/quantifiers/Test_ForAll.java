package dk.itu.openjml.quantifiers;

import java.util.ArrayList;
import java.util.List;

import org.jmlspecs.openjml.API;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import com.sun.tools.javac.tree.JCTree.JCParens;


public class Test_ForAll {
	
	List<String> qExprsJml;
	List<JmlQuantifiedExpr> qExprsAst;
	API openjmlApi;
	
	final static String FORALL_CLASS_HEAD = "class JML$ITU$ForAll"; 
	final static String FORALL_CLASS_TOP = "{ public static void forAll() {";
	final static String FORALL_CLASS_BOTTOM = "}}";
	
	// Do not remove escape sequences!
	final static String TEST_CLASS_HEAD = "class Test";
	final static String TEST_CLASS_TOP = "{\n";
	final static String TEST_CLASS_BOTTOM = "\npublic static void test() {}}";
	
	public void addExpressions(List<String> s) {
		s.add("//@ requires (\\forall int i; 0 <= i && i < 10; i < 10);"); 
		s.add("//@ requires (\\forall int i; i >= 5 || i < 10; i < 10);"); 
		s.add("//@ requires (\\forall int i; i >= 5 || i < 10 && i < 300; i > 0);"); 
		s.add("//@ requires (\\forall int i; i >= 5 || i < 10 && i < 300 && i != 500; i > 10 );"); 
		s.add("//@ requires (\\forall int i, j; 0 <= i && i < 10 && j == i++; i == (j - 1));");
		s.add("//@ requires (\\forall int i, j, h; 0 <= i && i < 10 && 50 < j && j <= 100; i == (j - 1));");
		s.add("//@ requires (\\forall int i; -100 < i && i < 0 || 0 < i && i < 100; i != 0);");
		// #27 
	}

	
	/**
	 * @param t AST containing JML-annotated Java sources
	 * @return Only the JmlQuantifiedExpr subtree
	 */
	public static JmlQuantifiedExpr pullOutQuantifier(JmlCompilationUnit t){
		if(t.defs.head instanceof JmlClassDecl){
			JmlClassDecl a = (JmlClassDecl)t.defs.head;
			if(a.defs.head instanceof JmlMethodDecl){
				JmlMethodDecl b = (JmlMethodDecl)a.defs.head;
				if(b.cases.cases.head.clauses.head instanceof JmlMethodClauseExpr){
					JmlMethodClauseExpr c = (JmlMethodClauseExpr)b.cases.cases.head.clauses.head;
					if(c.expression instanceof JCParens){
						JCParens d = (JCParens)c.expression;
						if(d.expr instanceof JmlQuantifiedExpr){
							return (JmlQuantifiedExpr)d.expr;
						}
					}
				}
			}
		}
		return null;
	}	
	

	@Before
	public void setUp() throws Exception {
		
		qExprsJml = new ArrayList<String>();
		qExprsAst = new ArrayList<JmlQuantifiedExpr>();
		addExpressions(qExprsJml);		
		
		openjmlApi = new API();
		
		// Add all expressions to AST list
		int count = 1;
		for(String s: qExprsJml) {
			JmlCompilationUnit t = openjmlApi.parseString("test$" + count, TEST_CLASS_HEAD + count + TEST_CLASS_TOP + s + TEST_CLASS_BOTTOM);
			qExprsAst.add(pullOutQuantifier(t));
			count++;
		}
	}

	@Test
	public void testForAll() {
		openjmlApi.setOption("-noPurityCheck");
		int count = 1;
		for(JmlQuantifiedExpr t: qExprsAst) {
			ForAll f = new ForAll(t);
			try{
				JmlCompilationUnit cForAll = openjmlApi.parseString("forAll$" + count, FORALL_CLASS_HEAD + count + FORALL_CLASS_TOP + f.translate() + FORALL_CLASS_BOTTOM);
				openjmlApi.enterAndCheck(cForAll);
			} catch (AssertionError a){
				// Ignore, as assertions are part of the code and should fail, given the \forall expression
			} catch (Exception e){
				Assert.fail(t.toString() + ", " + f.toString() + ", " + e.toString());
			} finally {
				count++;
			}
		}
	}

}
