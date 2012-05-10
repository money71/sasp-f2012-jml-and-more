/**
 *  jml2 refman:
 *  \fresh(x,y) asserts that x and y are not null and that the objects bound to
 *   these identifiers were not allocated in the pre-state. The arguments to \fresh...
 */
public class FreshArray {
    
	private static /*@ spec_public @*/ int[] a;
	
    /*@ assignable a; 
    @ ensures \fresh(a);
    @*/
    public static void foo () {
    	a = new int[2];
    	a[0] = 1;
    	a[1] = 1;
    }

    public static void main (String[] args){
    	foo();
    }
}