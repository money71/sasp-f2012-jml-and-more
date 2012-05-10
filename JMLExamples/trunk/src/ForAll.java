public class ForAll {
	
	//@ requires (\forall int i; 0 <= i && i < array.length; array[i] == i);
	public static void forAll (int[] array) {
		// Do nothing
	}
	
	public static void main (String[] args) {
		forAll(new int[] {0, 1, 2, 3});
	}
	
}