
// Minimal container class 
class Container {
	
	private Contained[] array;
	
	public Container (Contained[] array) {
		this.array = array;
	}
	
	public /*@ pure @*/ boolean contains (Contained i) {
		for (Contained j: array) {
			if (j == i) return true;
		}
		return false;
	}	
}

// Minimal contained class
class Contained {
	int value;
	
	public Contained (int value) {
		this.value = value;
	}
}

public class ForAllExtended {

	//@ requires (\forall Contained c; a.contains(c) && b.contains(c); 1 < c.value && c.value < 4);
	public static /*@ pure @*/ void forAllExtended(Container a, Container b){
		// Do nothing
	}
	
	public static void main(String[] args) {
		Contained A = new Contained(1);
		Contained B = new Contained(2);
		Contained C = new Contained(3);
		Contained D = new Contained(4);
		
		// Precondition should hold
		System.out.println("Precondition holds!");
		
		Container containerA = new Container(new Contained[] {A, B, C});
		Container containerB = new Container(new Contained[] {B, C, D});
		
		forAllExtended(containerA, containerB);
		
		// Precondition should fail
		System.out.println("Precondition fails!");
		
		Container containerC = new Container(new Contained[]{A, B, D});
		Container containerD = new Container(new Contained[]{B, C, D});
		
		forAllExtended(containerC, containerD);
	}

}
