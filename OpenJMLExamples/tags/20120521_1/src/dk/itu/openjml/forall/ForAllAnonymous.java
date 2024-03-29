package dk.itu.openjml.forall;

import java.util.ArrayList;
import java.util.List;

import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;


interface IPredicate {
	/* Usage of this class:
	 * 
	 * public void foo(IPredicate, int i){
	 * 		// Something...
	 * }
	 * 
	 * // The code below will print out "1".
	 * foo(new IPredicate(){
	 * 			public boolean check(Integer i){
	 * 				return i > 0;
	 * 			}
	 * 		}, 1);
	 */
	
	/**
	 * Evaluation of the predicate
	 * @param var the variable against which the predicate is checked
	 * @return True if it holds, false otherwise
	 */
	public /*@ pure @*/boolean check(Object var, /*@ nullable @*/ Object other);
}

public class ForAllAnonymous {
	/* This should combine the best of two worlds:
	 * On the one hand, we generate source code, on the
	 * other hand we use the given utility functions to
	 * actually perform the checks. The only thing that gets
	 * generated, apart from the function call, are the
	 * inline predicate functions.
	 */
	
	/**
	 * Generates code for RAC
	 * @param e A JmlQuantifiedExpr that should be translated into executable code
	 * @return A string (later a JmlExpression) holding the RAC code for this check
	 */
	public static String check(JmlQuantifiedExpr e){
		return "";
	}
	
	/**
	 * Instead of generating a simple predicate that should
	 * hold for a value of arbitrary type, we infer the
	 * range from the expression and return a list
	 * over which we iterate.
	 * @param e The range expression
	 * @return A list which represents the range
	 */
	static /*@ pure @*/ List<String> getRanges(JmlQuantifiedExpr e){
		// TODO: Implement!
		return new ArrayList<String>();
	}
		
	static /*@ pure @*/ List<IPredicate> getPredicates(JCExpression e){
		return new ArrayList<IPredicate>();
	}
	
	/**
	 * Checks a quantified expression for exactly one variable.
	 * @param range A list representing the range of the quantifier
	 * @param predicates A list of predicate objects
	 * @return True if all predicates hold for each element of range
	 */
	public static /*@ pure @*/ boolean checkForAll(List<Object> range, List<IPredicate> predicates, Object declarations){
		for(Object i: range){
			for(IPredicate p: predicates){
				if(!p.check(i, declarations)){
					return false;
				}
			}
		}
		return true;
	}
}
