/**
 *  Not fresh version of Fresh.java should fail on run time when rac complied 
 */
public class FreshNotFresh {
    
	private static /*@ spec_public @*/ Object a;		
	
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