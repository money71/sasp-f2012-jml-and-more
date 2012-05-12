package dk.itu.openjml.test;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import org.jmlspecs.openjml.API;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCParens;

import dk.itu.openjml.forall.ForAllNaive;

public class Test_ForAllNaive {
	
	List<String> qExprsJml;
	List<JmlQuantifiedExpr> qExprsAst;
	API openjmlApi;
	
	public void addExpressions(List<String> s) {
		//s.add("//@ requires (\\forall int i; ;);"); // Illegal expression?
		s.add("//@ requires (\\forall int i; 0 <= i && i < 10; i < 10);"); // Always true
		s.add("//@ requires (\\forall int i; 0 <= i && i < 10; a[i]);"); // Is this legal if there is no a declared?
		s.add("//@requires (\\forall int i, j; 0 <= i && i < 10 && j == i++; i == (j - 1));");
		
		// TODO: Add more expressions!
	}
	
	/**
	 * @param t AST containing JML-annotated Java sources
	 * @return Only the JmlQuantifiedExpr subtree
	 */
	public static JmlQuantifiedExpr pullOutQuantifier(JmlCompilationUnit t){
		
		// FIXME: Ugliest hack I've written in a while.
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
		for(String s: qExprsJml) {
			qExprsAst.add(pullOutQuantifier(openjmlApi.parseString("test", "class Test {\n\t" + s + "\n\t public static void test() {}\n}")));
		}
	}

	@Test
	public void testGenerateForAll() {
		for(JmlQuantifiedExpr t: qExprsAst) {
			try{
				openjmlApi.parseString("forAllTest", "class ForAllTest {\n" + ForAllNaive.generateForAll(t) + "\n}");
			} catch (Exception e){
				Assert.fail(e.toString());
			}
		}
	}

	@Test
	public void testAssertForAll() {
		for(JmlQuantifiedExpr t: qExprsAst) {
			Assert.assertEquals(null, true, ForAllNaive.assertForAll(t));
		}
	}

}
