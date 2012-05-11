/**
 *  jml2 refman:
 *  \fresh(x,y) asserts that x and y are not null and that the objects bound to
 *   these identifiers were not allocated in the pre-state. The arguments to \fresh...
 *   
 *  - some examples in the mobious project just use \fresh(\result) 
 */
public class FreshResult {
	 
    //@ ensures \fresh(\result);
    public static Object foo () {
    	return new Object();
    }

    public static void main (String[] args){
    	foo();
    }
}