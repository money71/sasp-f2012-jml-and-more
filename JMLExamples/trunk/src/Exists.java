public class Exists {

	//@ requires (\exists int i; 0 <= i && i < array.length; array[i] == 1);
	public static void exists (int[] array) {
		// Do nothing
	}
	
	public static void main(String[] args) {
		System.out.println("Precondition holds!");
		exists(new int[] {1});
		System.out.println("Precondition fails!");
		exists(new int[] {0});
	}

}
