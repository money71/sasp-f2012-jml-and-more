package dk.itu.openjml.forall;

import org.jmlspecs.openjml.API;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;

public class ForAllNaive {
	
	/**
	 * 
	 * @param tree JML AST containing a \forall expression
	 * @return Java code that asserts the given \forall expression
	 */
	public static String generateForAll(JmlQuantifiedExpr tree) {
		
		return tree.toString();
	}
	
	/**
	 * 
	 * @param tree JML AST containing a \forall expression
	 * @return True if the \forall expression holds, false otherwise
	 */
	public static boolean assertForAll(JmlQuantifiedExpr tree) {
		
		return true;
	}
}
