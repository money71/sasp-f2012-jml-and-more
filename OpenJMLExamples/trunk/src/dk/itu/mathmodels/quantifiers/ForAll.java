package dk.itu.mathmodels.quantifiers;

/**
 * 
 * How do we represent an universal quantifier in Java...
 * 
 * (forall int i; 0 <= i; i <= 10; P(i))
 * requires (\forall int i; 0 <= i && i < array.length; array[i] == i);
 * 
 * For now we have used JML specifications in the code to be clear 
 *
 */
public class ForAll {
	
	/**
	 * Some function P - for which the forall should hold
	 * 
	 * - according to JML 2 the method has to be pure to 
	 *   be used specified as predicate in a quantifier expression.
	 *   
	 * - JML 2 don't like this to be a boolean / int - why ?
	 *   raises:
	 *   "error: Syntax error: unexpected token : int"
	 *   "error: Syntax error: unexpected token : boolean"
	 */
	public static int /*@ pure @*/ intPredicate(int i) {
		return i;
	}
	public static boolean /*@ pure @*/ boolPredicate(int i) {
		return i < 10;
	}

	
	//@ requires (\forall int i; 0 <= i && i < 10; i == intPredicate(i));
	public static boolean forall() {
		boolean auxileryResult = true;
		for (int i = 0; i < 10; i++) {
			boolean result = i == intPredicate(i); 
			assert(result);
			if (!result)
				auxileryResult = false;
		}		
		return auxileryResult;
	}

	//@ requires (\forall int i; 0 <= i && i < 10; i == boolPredicate(i));
	public static boolean forallBreak() {
		boolean auxileryResult = true;
		for (int i = 0; i < 10; i++) {
			boolean result = boolPredicate(i); 
			assert(result);
			if (!result) {
				auxileryResult = false;
				break;
			}
		}		
		return auxileryResult;
	}
	
	
	//@ requires (\forall int i; 0 <= i && i < 10; boolPredicate(i));
	public static boolean forallJavaInts() {
		boolean auxileryResult = true;
		for (int i = Integer.MIN_VALUE; i <= Integer.MAX_VALUE; i++) {
			boolean result = (0 <= i && i < 10 && boolPredicate(i));
			assert(result);
			if (!result)
				auxileryResult = false;
		}		
		return auxileryResult;
	}
	
	//@ requires (\forall int i; ;);
	public static void forallJavaIntsNoPredicates() {
		for (int i = Integer.MIN_VALUE; i <= Integer.MAX_VALUE; i++) {
			// do nothing;
		}
	}
		
}