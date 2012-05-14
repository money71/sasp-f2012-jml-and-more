
class Foo {
	public int value;
	
	public Foo(int value){
		this.value = value;
	}
	
	public /*@ pure @*/ boolean p(){
		System.out.println("Evaluation in Foo was executed!");
		return value > 10;
	}
}

class Bar {
	private int value;
	
	public Bar(int value){
		this.value = value;
	}
	
	public /*@ pure @*/ int getValue(){
		return this.value;
	}
	
	public /*@ pure @*/ boolean p(){
		System.out.println("Evaluation in Bar was executed!");
		return this.getValue() > 10;
	}
}

public class ForAllBorderCase {
	
	//@ requires (\forall Foo f; 10 < f.value && f.value < 20; f.p()); 
	public static void forAllBorderCaseFoo(){
		// Do nothing
	}
	
	//@ requires (\forall Bar b; 10 < b.getValue() && b.getValue() < 20; b.p());
	public static void forAllBorderCaseBar(){
		// Do nothing
	}
	
	public static void main(String[] args) {
		forAllBorderCaseFoo();
		forAllBorderCaseBar();
	}

}
