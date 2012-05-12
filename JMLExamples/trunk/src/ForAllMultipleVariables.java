
public class ForAllMultipleVariables {

    // - not valid using: ++ http://code.google.com/p/sasp-f2012-jml-and-more/issues/detail?id=8
	//@ requires (\forall int i, j; 0 <= i && i < array.length && j == i++; array[i] == j);
	public static void forAllMultipleVars (int[] array) {
		// Do nothing
	}
	
	public static void main(String[] args) {
		//System.out.println("Precondition holds!");
		//forAllMultipleVars(new int[] {1, 2, 3});
		
		System.out.println("Precondition fails!");
		forAllMultipleVars(new int[] {1, 2, 4});
	}

}
