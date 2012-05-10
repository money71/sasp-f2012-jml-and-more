public class Exists {

	//@ requires (\exists int i; 0 <= i && i < array.length; array[i] == 1);
	public static void exists (int[] array) {
		// Do nothing
	}
	
	public static void main(String[] args) {
		exists(new int[] {1});
	}

}
