package dk.itu.functional.functions;

/*
 * Supports functions taking a type A 
 * and returning a value of Type R
 * 
 * Based upon xxx - add ref to functional java book
 * and an approach also used in the http://functionaljava.org
 * 
 */
public interface Function1<A, R> {
	  R apply(A a);
	}