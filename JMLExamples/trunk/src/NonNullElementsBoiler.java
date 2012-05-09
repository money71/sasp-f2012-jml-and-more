public class NonNullElementsBoiler {
    
    /**
     * Performs nullity-check until the first null reference is found.
     *
     * @param Object[] o Array which should be checked for \nonnullelements
     * @returns True if no element in o is null, false otherwise
     */
    //@ requires o != null;
    //@ requires (\forall int i; 0 <= i && i < o.length; o[i] != null);
    //@ ensures \result == true;
    //@ also
    //@ requires o == null || (\exists int i; 0 <= i && i < o.length; o[i] == null);
    //@ ensures \result == false;
    public static boolean nonNullElementsfirstOccurence(Object[] o){
	//	for (Object i: o) {
	for (int i = 0; i < o.length; i++) {
	    //	    if (i == null) return false;
	    if (o[i] == null) return false;
	}
	return true;
    }
    
    /**
     * Performs nullity-check on _each_ object in the array, then
     * returns the result.
     *
     * @param Object[] o Array which should be checked for \nonnullelements
     * @returns True if no element in o is null, false otherwise
     */
    //@ requires o != null;
    //@ requires (\forall int i; 0 <= i && i < o.length; o[i] != null);
    //@ ensures \result == true;
    //@ also
    //@ requires o == null || (\exists int i; 0 <= i && i < o.length; o[i] == null);
    //@ ensures \result == false;
    public static boolean nonNullElementsAll(Object[] o){
	boolean retval = true;
	//	for (Object i: o) {
	for (int i = 0; i < o.length; i++) {
	    //	    retval = retval && i != null;
	    retval = retval && o[i] != null;
	}
	return retval;
    }
    
    // TODO: Double-check specs!
    // TODO: JML2 cannot cope with iterators (1.4 syntax).
    // TODO: Should we also try a recursive function?
    // TODO: What about multi-dimensional arrays?
}