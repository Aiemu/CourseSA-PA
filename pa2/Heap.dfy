////////////////////////////////////////////////////////////////////////////////////
// PA 2
// Problem 1: A Verified Heap 70%
////////////////////////////////////////////////////////////////////////////////////

datatype Heap = H(a: array?<int>, size: int, capacity: int)

predicate valid_heap(h: Heap)
	reads h.a
{
	h.a != null && h.a.Length == h.capacity + 1 && 0 <= h.size <= h.capacity &&
	    forall i :: 1 < i <= h.size ==> h.a[i] <= h.a[i / 2]
}

method init_heap(cap: int) returns (h: Heap)
	requires 0 <= cap
	ensures valid_heap(h)
	ensures h.size == 0 && h.capacity == cap
	ensures fresh(h.a)
{
	var a := new int[cap + 1];
	h := H(a, 0, cap);
}

method insert(x: int, h: Heap) returns (h': Heap)
	requires valid_heap(h)
	requires h.size < h.capacity
	ensures valid_heap(h')
	ensures h'.size == h.size + 1 && h'.capacity == h.capacity
	ensures fresh(h'.a)
{
	// init
	var a := new int[h.capacity + 1];
	var idx := 1;

	while (h.size >= idx)
		decreases h.size - idx
		invariant (forall j :: 1 <= j < idx ==> j <= h.size && a[j] == h.a[j])
	{
		a[idx] := h.a[idx];

		idx := idx + 1;
	}
	
	// add the new node into array
	var cur_cap := h.size + 1;
	a[cur_cap] := x;

	// adjust the location of the new node in the heap
	if (cur_cap > 1) 
	{
		// compare and change
		if (a[cur_cap / 2] <= a[cur_cap]) 
		{
			var swap := a[cur_cap / 2];

			a[cur_cap / 2] := a[cur_cap];
			a[cur_cap] := swap;
		}

		var parent := cur_cap / 2;

		// check the properties of max heap
		assert ((2 * parent != cur_cap) ==> ((cur_cap - 1) / 2 == cur_cap / 2));
		assert ((2 * parent + 1 <= cur_cap) ==> (a[2 * parent + 1] <= a[parent]));

		assert (a[2 * parent] <= a[parent]);
		
		assert ((parent > 1) ==> (a[2 * parent] <= a[parent / 2]));
		assert ((parent > 1 && 2 * parent + 1 <= cur_cap) ==> (a[2 * parent + 1] <= a[parent / 2]));

		// adjust the heap again and check Max heap on time
		while (parent > 1) 
			decreases parent
			invariant (parent >= 0)
			invariant ((parent > 1) ==> (a[2 * parent] <= a[parent / 2]))
			invariant ((parent > 1 && 2 * parent + 1 <= cur_cap) ==> (a[2 * parent + 1] <= a[parent / 2]))
			invariant (forall i :: 1 < i < parent ==> a[i] <= a[i / 2])
			invariant (forall i :: parent < i <= cur_cap ==> a[i] <= a[i / 2])
		{	
			// assert the correct node
			assert ((parent / 2 * 2 != parent) ==> ((parent - 1) / 2 == parent / 2));
			assert ((parent / 2 * 2 == parent) ==> ((parent + 1) / 2 == parent / 2));	

			// swap
			if (a[parent / 2] <= a[parent])
			{
				var swap := a[parent / 2];

				a[parent / 2] := a[parent];
				a[parent] := swap;
			}

		// get parent and move to the upper level
			parent := parent / 2;
		}

		// get h'
		h' := H(a, cur_cap, h.capacity);

	} 
	else 
	{
	// root node
		h' := H(a, cur_cap, h.capacity);
	}
}

// check if child
predicate checkChild(r: int, s: int)
	requires r >= 1
	requires s >= 1
	decreases s
{
	if (s == r)
		then true
	else if (s < r)
		then false
	else
		checkChild(r, s / 2)
}

// check if root
lemma checkRoot(h: Heap, x: int)
	requires valid_heap(h)
	requires x >= 1
	ensures forall i :: x < i <= h.size && checkChild(x, i) ==> h.a[x] >= h.a[i]
{}

// check if child of root
lemma checkRootChild(h: Heap) 
	requires valid_heap(h)
	requires h.size >= 1
	ensures forall i :: 1 <= i <= h.size ==> checkChild(1, i)
{}

// check valued root
lemma checkRootValue(h: Heap)
	requires valid_heap(h)
	requires h.size >= 1
	ensures forall i :: 1 <= i <= h.size ==> h.a[1] >= h.a[i]
{
	checkRootChild(h);
	checkRoot(h, 1);
}

method extract(h: Heap) returns (x: int, h': Heap)
	requires valid_heap(h)
	requires 0 < h.size
	ensures valid_heap(h')
	ensures h'.size == h.size - 1
	ensures fresh(h'.a)
	ensures x == h.a[1]
	ensures forall i :: 1 <= i <= h'.size ==> x >= h'.a[i]
{
	// init
	var a := new int[h.capacity + 1];
	var idx := 1;

	while (idx <= h.size)
		decreases h.size - idx
		invariant (forall j :: 1 <= j < idx ==> h.size >= j && h.a[j] == a[j])
	{
		a[idx] := h.a[idx];

		idx := idx + 1;
	}

	// check root of h
	checkRootValue(h);

	x := a[1]; // root
  
	a[1] := a[h.size];
	a[h.size] := x;
  
	var cur_cap := h.size - 1;

	// adjust the heap
	var parent := 1;
	while (cur_cap >= 2 * parent)
		decreases cur_cap - parent
		invariant ((parent > 1 && 2 * parent <= cur_cap) ==> (a[parent / 2] >= a[2 * parent]))
		invariant ((parent > 1 && 2 * parent + 1 <= cur_cap) ==> (a[parent / 2] >= a[2 * parent + 1]))
		invariant (forall i :: 1 <= i <= cur_cap ==> x >= a[i])
		invariant (forall i :: 1 < i <= cur_cap && i != 2 * parent && i != 2 * parent + 1 ==> a[i / 2] >= a[i])
	{
		var child := 2 * parent;

		if (2 * parent + 1 <= cur_cap && a[2 * parent + 1] >= a[2 * parent]) 
		{
			child := 2 * parent + 1;
		}

		assert (child == child * 2 / 2);
		assert (child == (child * 2 + 1) / 2);

		// swap
		if (a[child] >= a[parent]) 
		{
			var swap := a[parent];

			a[parent] := a[child];
			a[child] := swap;
		}
		
		parent := child;
	}
	h' := H(a, cur_cap, h.capacity);
}

////////////////////////////////////////////////////////////////////////////////////
// PA 2
// Problem 2: Heapsort 30%
////////////////////////////////////////////////////////////////////////////////////

class Heapsort
{
	var h: Heap;

	method sort(a: array?<int>)
		requires a != null && 0 <= a.Length
		ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] >= a[i + 1]
		modifies this, h.a, a
	{
		h := init_heap(a.Length + 1);

		// create max heap
		var tail := 0; 
		while (tail < a.Length) 
			decreases a.Length - tail
			invariant valid_heap(h)
			invariant (a.Length < h.capacity)
			invariant (a.Length >= tail)
			invariant (h.size == tail)
		{
			h := insert(a[tail], h);
			tail := tail + 1;
		}
		
		// extract the root and get sorted arrat
		tail := 0;
		while (tail < a.Length)
			decreases a.Length - tail
			invariant valid_heap(h)
			invariant (a.Length == h.size + tail)
			invariant (0 <= tail <= a.Length)
			invariant (forall i :: 0 <= i < tail - 1 ==> a[i] >= a[i + 1])
			invariant (forall i :: 1 <= i <= h.size && tail > 0 ==> a[tail - 1] >= h.a[i])
		{
			a[tail], h := extract(h);
			tail := tail + 1;

			assert (tail >= 2 ==> a[tail - 2] >= a[tail - 1]);
		}

	}
}
