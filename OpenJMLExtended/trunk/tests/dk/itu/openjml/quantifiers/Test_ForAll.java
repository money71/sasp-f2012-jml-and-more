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
	
	public void addExpressions(List<String> s) {
		//s.add("//@ requires (\\forall int i; ;);"); // Illegal expression?
		// do we mean:
		//s.add("//@ requires (\\forall int i; ; ;"); // Illegal expression?
		s.add("//@ requires (\\forall int i; 0 <= i && i < 10; i < 10);"); // Always true
				
		s.add("//@ requires (\\forall int i; i >= 5 || i < 10; i < 10);"); // Not always true
		s.add("//@ requires (\\forall int i; i >= 5 || i < 10 && i < 300; i > 0);"); // Always true
		
		// FIXME: what about set difference / !=
		//s.add("//@ requires (\\forall int i; i >= 5 || i < 10 && i < 300 && i != 500; i > 10 );"); // Always true
		s.add("//@ requires (\\forall int i; 0 <= i && i < 10; a[i]);"); // Is this legal if there is no a declared?
		s.add("//@ requires (\\forall int i, j; 0 <= i && i < 10 && j == i++; i == (j - 1));");
		s.add("//@ requires (\\forall int i, j, h; 0 <= i && i < 10 && 50 < j && j <= 100; i == (j - 1));");
		s.add("//@requires (\\forall Foo f; f.value < 0; f.cool());");
		s.add("//@ requires (\\forall int i; -100 < i && i < 0 || 0 < i && i < 100; i != 0);");
		
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
	public void testForAll() {
		for(JmlQuantifiedExpr t: qExprsAst) {
			System.out.println(t);
			ForAll p;			
			try{
				p = new ForAll(t);
				System.out.println(p.translate());
			} catch (Exception e){
				Assert.fail(e.toString());
			}
		}
	}

}
