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
	 * - and always remember to have the / * @ pure @ * / before
	 *   the type declaration. 
	 */
	public static /*@ pure @*/ int intPredicate(int i) {
		return i;
	}
	public static /*@ pure @*/ boolean boolPredicate(int i) {
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
	
	
    
	
	//@ requires (\forall int i; 0 <= i && i < array.length; array[i-1] == i);
    public static boolean forallArray (int[] array) { 
    	int i = 0 + 1; // hmm hack
    	// here he can move in the whole guard
    	while(0 <= i && i < array.length){
    		System.out.println(i);
			boolean result = (0 <= i && i < array.length && array[i-1] == i);
			// can we have more predicates than [array[i-1] == i] ?
			assert(result);
    		i++;
    	}
    	return true;
    }
	
    // - not valid using: ++ http://code.google.com/p/sasp-f2012-jml-and-more/issues/detail?id=8
    // @ requires (\forall int i, j; 0 <= i && i < array.length && j == i++; array[i] == j);
    //@ requires (\forall int i, j; 0 <= i && i < array.length && j == i; array[i] == j);
    public static boolean forallArray2 (int[] array) {
    	// how do we know i start at 1 ?
    	int i = 0, j = 0;
    	// here he can move in the whole guard
    	while(0 <= i && i < array.length && j == i++){
    		System.out.println(i);
			boolean result = (array[i] == j);
			assert(result);
    		i++;
    		j++;
    	}
    	return true;
    }
	
		
}