/**
 *  jml2 refman:
 *  \fresh(x,y) asserts that x and y are not null and that the objects bound to
 *   these identifiers were not allocated in the pre-state. The arguments to \fresh...
 */
public class FreshNotFresh {
    
	private static Object a = null;	
	
    /*@ assignable a; 
    @ ensures \fresh(a);
    @*/
    public static Object foo () {
    	//a = new Object();
    	return a;
    }

    public static void main (String[] args){
    	foo();
    }
}