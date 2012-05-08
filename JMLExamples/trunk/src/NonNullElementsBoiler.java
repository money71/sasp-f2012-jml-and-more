public class NonNullElementsBoiler {
    
    /**
     * TODO: Write specs?
     *
     * Performs nullity-check until the first null reference is found.
     *
     * @param Object[] o Array which should be checked for \nonnullelements
     * @returns True if no element in o is null, false otherwise
     */
    public static boolean nonNullElementsfirstOccurence(Object[] o){
	for (int i = 0; i < o.length; i++) {
	    if (o[i] == null) return false;
	}
	return true;
    }
    
    /**
     * TODO: Write specs?
     *
     * Performs nullity-check on _each_ object in the array.
     *
     * @param Object[] o Array which should be checked for \nonnullelements
     * @returns True if no element in o is null, false otherwise
     */
    public static boolean nonNullElementsAll(Object[] o){
	boolean retval = true;
	for (int i = 0; i < o.length; i++) {
	    retval = retval && !(o[i] == null);
	}
	return retval;
    }
    
    // TODO: Should we also try a recursive function?
}