
public class Sum {
	
	// Basically says that v cannot be 0
	//@ requires 1 <= (\sum int i; 0 < i && i < 10; i * v);
	public static void sum (int v) {
		// Do nothing
	}
	
	public static void main(String[] args) {
		System.out.println("Precondition holds!");
		sum(1);
		
		System.out.println("Precondition fails!");
		sum(0);
	}

}
