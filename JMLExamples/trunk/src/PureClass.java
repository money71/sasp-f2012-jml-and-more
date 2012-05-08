/**
 * 
 * Spec pure for the whole class should set all methods to be pure...
 *
 */
public class /*@ pure @*/ PureClass {
 
	public static int pure1() {
		return 1;
	}

	public static int pure2() {
		return 2;
	}
	
    public static void main (String[] args){
    	pure1();
    	pure2();
    }

}