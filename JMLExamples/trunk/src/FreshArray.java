/**
 *  jml2 refman:
 *  \fresh(x,y) asserts that x and y are not null and that the objects bound to
 *   these identifiers were not allocated in the pre-state. The arguments to \fresh...
 *   
 *   \fresh usage think resize() of data structures e.g. using array for storage
 *   hash map, bag/stack etc.
 */
public class FreshArray {

	private static /*@ spec_public @*/ int[] a = new int[1];
	
    /*@ assignable a; 
    @ ensures \fresh(a);
    @*/
    public static void foo () {
    	a = new int[2*a.length+1];
    	a[0] = 1;
    	a[1] = 2;
    	a[2] = 3;
    }

    public static void main (String[] args){
    	foo();
    }
}