package dk.itu.openjml.forall;

import java.util.ArrayList;
import java.util.List;

import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;

public class ForAllSetBased {
	/*
	 * This is a first attempt to formulate a class as outlined in
	 * http://code.google.com/p/sasp-f2012-jml-and-more/wiki/ApproachTowardsQuantifiers
	 * 
	 * FIXME: The class is not pure but all the methods are. Should instead the class be pure?
	 * 
	 * TODO: Implement generateCheck - basic call structure.
	 * TODO: Implement generateDeclaration - figure out which race variables need to be declared.
	 * TODO: Implement generateForLoop - build a (nested)for-loop of the form {{{for(T t: S)...}}}
	 * TODO: Implement generatePredicate - generate a proper predicate check - maybe replace with something more general?
	 * TODO: Implement evaluateRange - probably the hardest one here, generate a set (collection) at runtime of values to iterate over.
	 * TODO: How to formulate a range-expression that can be evaluated at runtime?
	 */
	
	// TODO: Write specs
	public static /*@ pure @*/ String generateCheck(JmlQuantifiedExpr e){
		// TODO: call generateForLoop()
		return "";
	}
	
	// TODO: Write specs
	public static /*@ pure @*/ <T> List<T> evaluateRange(){
		return new ArrayList<T>();
	}
	
	// TODO: Write specs
	private static /*@ pure @*/ String generateForLoop(){
		// TODO: call generateDeclaration();
		// TODO: call generatePredicate();
		return "";
	}
	
	// TODO: Write specs
	private static /*@ pure @*/ String generateDeclaration(){
		return "";
	}
	
	// TODO: Write specs
	private static /*@ pure @*/ String generatePredicate(){
		return "";
	}
}
