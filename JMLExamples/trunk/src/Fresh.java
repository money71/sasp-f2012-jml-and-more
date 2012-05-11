/**
 *  jml2 refman:
 *  \fresh(x,y) asserts that x and y are not null and that the objects bound to
 *   these identifiers were not allocated in the pre-state. The arguments to \fresh...
 */
public class Fresh {
    
	private static /*@ spec_public @*/ Object a;	
	
//	"warning: Entire clause will be dropped since JmlFreshExpression is not executable" ?
	
    /*@ assignable a; 
    @ ensures \fresh(\result);
    @*/
    public static Object foo () {
    	/* in the jml 2 tutorial they uses rep but since universes is not 
    	 * implemented in openjml yet 
    	 * - we should use that for now - right ?
    	 * a = new / * @ rep @ * / int[inp.length]; */
    	return new Object();
    }

    public static void main (String[] args){
    	foo();
    }
}