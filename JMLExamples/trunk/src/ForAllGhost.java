/**
 * 
 * Based upon the OpenJML/tests/tests/rac.java
 *
 */
public class ForAllGhost {
		
	public static void main (String[] args) {
	
		//@ ghost boolean n = (\forall int i; 0<=i && i<=5; i >= 0);
		// @ ghost boolean nn = (\exists int i; 0<=i && i<=5; i >= 6);
		// @ debug System.out.println("A " + n + " " + nn);
	}
	
}