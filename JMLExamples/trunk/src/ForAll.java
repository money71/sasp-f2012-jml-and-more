public class ForAll {
	
	//@ requires (\forall int i; 0 <= i && i < array.length; array[i] == i);
	public static void forAll (int[] array) {
		// Do nothing
	}
	
	public static void main (String[] args) {
		System.out.println("Precondition holds!");
		forAll(new int[] {0, 1, 2, 3});
		
		System.out.println("Precondition fails!");
		forAll(new int[] {0, 1, 1, 3});
	}
	
}