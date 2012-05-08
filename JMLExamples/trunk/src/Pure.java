public class Pure {
 
	public static /*@ pure @*/ int pure() {
		return 6;
	}
	
    public static void main (String[] args){
    	pure();
    }

}