package dk.itu.openjml.forall;

import java.util.ArrayList;
import java.util.List;

import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;

import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.ListBuffer;

public class ForAllNaive {
	
	/**
	 * Converts a JmlQuantifiedExpr into executable code which is returned as a String
	 * @param tree JML AST containing a \forall expression
	 * @return Java code that asserts the given \forall expression
	 */
	public static String generateForAll(JmlQuantifiedExpr tree) {
		
		// Storing the code
		String generated = "static boolean assertForAll(){\n\t";
		int lBrackCount = 0;
		
		List<String> forLoops = getForLoop(tree.decls);
		List<String> ranges = getRangeExpression(tree.range);
		List<String> predicates = getPredicate(tree.value);
		
		// Adding for loops
		for(String s: forLoops){
			generated += s + "\n";
			lBrackCount++;
		}
		
		// Adding range expression check
		generated += "if(";
		for(String s: ranges){
			generated += "(" + s + ")" + " && "; 
		}
		
		// Adding predicate assertion
		generated += "true){\nif(!(";
		for(String s: predicates){
			generated += "(" + s + ")" + " && ";
		}
		
		// Finishing syntax
		generated += "true)){\n\treturn false;\n}\n}";
		while(lBrackCount > 0){
			generated += "\n}";
			lBrackCount--;
		}
		
		// Default return
		generated += "\nreturn true;\n}";
		return generated;
	}
	
	private static List<String> getForLoop(ListBuffer<JCVariableDecl> e){
		List<String> forLoops = new ArrayList<String>();
		
		for(JCVariableDecl d: e){
			// Generate a for-loop for each integer declared
			forLoops.add("for(" + d.toString()
							+ " = Integer.MIN_VALUE; "
							+ d.name + " <= Integer.MAX_VALUE; "
							+ d.name + "++) {");
		}		
		return forLoops;
	}
	
	private static List<String> getRangeExpression(JCExpression e){
		List<String> ranges = new ArrayList<String>();
		
		// We just take the whole expression as one assertion
		ranges.add(e.toString());
		return ranges;
	}
	
	private static List<String> getPredicate(JCExpression e){
		List<String> predicates = new ArrayList<String>();
		
		// We just take the whole expression as one assertion
		predicates.add(e.toString());
		return predicates;
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
