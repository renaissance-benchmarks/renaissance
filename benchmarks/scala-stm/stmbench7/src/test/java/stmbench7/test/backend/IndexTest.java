package stmbench7.test.backend;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.Iterator;
import java.util.Random;
import java.util.TreeMap;

import org.junit.Before;
import org.junit.Test;

import stmbench7.backend.BackendFactory;
import stmbench7.backend.Index;
import stmbench7.impl.backend.BackendFactoryImpl;

/**
 * JUnit test for an Index class.
 */
public class IndexTest {

	/**
	 * Change the factory to test other implementation.
	 */
	protected BackendFactory backendFactory;
	
	private Index<Integer,Integer> index, emptyIndex;
	
	public IndexTest() {
		backendFactory = new BackendFactoryImpl();
	}
	
	@Before
	public void setUp() throws Exception {
		index = backendFactory.createIndex();
		emptyIndex = backendFactory.createIndex();
		
		for(int key = 0; key < 100; key++) {
			int val = key * 2;
			index.put(key, val);
		}
		
		for(int key = 100; key >= 0; key -= 2) {
			int val = key;
			index.put(key, val);
		}
	}

	/**
	 * Test method for {@link stmbench7.impl.backend.TreeMapIndex#put(stmbench7.backend.IndexKey, java.lang.Object)}.
	 */
	@Test
	public void testPut() {
		emptyIndex.put(5, 10);
		emptyIndex.put(10, 11);
		emptyIndex.put(1, 12);
		emptyIndex.put(7, 10);
		assertTrue(emptyIndex.get(5) == 10);
		assertTrue(emptyIndex.get(10) == 11);
		assertTrue(emptyIndex.get(1) == 12);
		assertTrue(emptyIndex.get(7) == 10);
	}

	/**
	 * Test method for {@link stmbench7.impl.backend.TreeMapIndex#putIfAbsent(stmbench7.backend.IndexKey, java.lang.Object)}.
	 */
	@Test
	public void testPutIfAbsent() {
		assertNull(index.putIfAbsent(101, 111));
		assertNull(index.putIfAbsent(-101, 111));
		assertTrue(index.putIfAbsent(10, 111) == 10);
		assertTrue(index.putIfAbsent(-101, 222) == 111);
		assertTrue(index.get(10) == 10);		
		assertTrue(index.get(-101) == 111);		
	}

	/**
	 * Test method for {@link stmbench7.impl.backend.TreeMapIndex#get(stmbench7.backend.IndexKey)}.
	 */
	@Test
	public void testGet() {
		assertNull(emptyIndex.get(4));
		assertNull(index.get(101));
		assertNull(index.get(-101));

		for(int key = 0; key <= 100; key += 2)
			assertTrue(index.get(key) == key);
		for(int key = 1; key <= 100; key += 2)
			assertTrue(index.get(key) == key * 2);
	}

	/**
	 * Test method for {@link stmbench7.impl.backend.TreeMapIndex#getRange(stmbench7.backend.IndexKey, stmbench7.backend.IndexKey)}.
	 */
	@Test
	public void testGetRange() {
		Iterator<Integer> range = index.getRange(5, 9).iterator();
		assertTrue(range.next() == 10);
		assertTrue(range.next() == 6);
		assertTrue(range.next() == 14);
		assertTrue(range.next() == 8);
		assertFalse(range.hasNext());
		
		range = index.getRange(-5, 2).iterator();
		assertTrue(range.next() == 0);
		assertTrue(range.next() == 2);
		assertFalse(range.hasNext());
		
		range = index.getRange(98, 120).iterator();
		assertTrue(range.next() == 98);
		assertTrue(range.next() == 99 * 2);
		assertTrue(range.next() == 100);
		assertFalse(range.hasNext());

		range = index.getRange(110, 120).iterator();
		assertFalse(range.hasNext());
		range = index.getRange(-120, -110).iterator();
		assertFalse(range.hasNext());

		range = emptyIndex.getRange(110, 120).iterator();
		assertFalse(range.hasNext());
	}

	/**
	 * Test method for {@link stmbench7.impl.backend.TreeMapIndex#remove(stmbench7.backend.IndexKey)}.
	 */
	@Test
	public void testRemove() {
		assertFalse(emptyIndex.remove(4));
		assertFalse(index.remove(200));
		assertFalse(index.remove(-20));

		assertTrue(index.remove(20));
		assertFalse(index.remove(20));
		assertNull(index.get(20));
		
		assertTrue(index.remove(50));
		assertFalse(index.remove(50));
		assertNull(index.get(50));

		assertTrue(index.remove(0));
		assertFalse(index.remove(0));
		assertNull(index.get(0));

		assertTrue(index.remove(100));
		assertFalse(index.remove(100));
		assertNull(index.get(100));
	}

	/**
	 * Test method for {@link stmbench7.impl.backend.TreeMapIndex#iterator()}.
	 */
	@Test
	public void testIterator() {
		Iterator<Integer> it = emptyIndex.iterator();
		assertFalse(it.hasNext());
		
		int key = 0;
		for(int val : index) {
			if(key % 2 == 0) assertEquals(val, key);
			else assertEquals(val, key * 2);
			assertTrue(key <= 100);
			key++;
		}
		assertEquals(key, 101);
	}
	
	@Test
	public void randomTest() {
		final int N = 10000;
		long time = System.currentTimeMillis();
		
		Index<Integer,Integer> randomIndex = backendFactory.createIndex();
		TreeMap<Integer,Integer> refIndex = new TreeMap<Integer,Integer>();

		Random random = new Random();
		int max = Integer.MIN_VALUE, min = Integer.MAX_VALUE;
		for(int n = 0; n < N; n++) {
			int key = random.nextInt();
			assertEquals(randomIndex.get(key), refIndex.get(key));
			randomIndex.put(key, key);
			assertTrue(randomIndex.get(key) == key);
			
			refIndex.put(key, key);
			
			max = Math.max(max, key);
			min = Math.min(min, key);
		}

		for(int n = 0; n < N; n++) {
			int key = random.nextInt();
			Integer val = randomIndex.putIfAbsent(key, key);
			assertEquals(refIndex.get(key), val);
			if(val == null) refIndex.put(key, key);
		}

		Iterator<Integer> it = randomIndex.iterator(), refIt = refIndex.values().iterator();
		int prevVal = Integer.MIN_VALUE;
		while(it.hasNext() && refIt.hasNext()) {
			int val = it.next(), refVal = refIt.next();
			assertTrue(val > prevVal);
			assertEquals(val, refVal);
			prevVal = val;
		}
		assertFalse(it.hasNext());
		assertFalse(refIt.hasNext());
		
		it = randomIndex.getRange(min/2, max/2).iterator();
		refIt = refIndex.subMap(min/2, max/2).values().iterator();
		while(it.hasNext()) 
			assertEquals(it.next(), refIt.next());
		assertFalse(refIt.hasNext());
		
		for(int n = 0; n < N; n++) {
			int key = random.nextInt();
			boolean res = randomIndex.remove(key);
			boolean refRes = ( refIndex.remove(key) != null ); 
			assertEquals(refRes, res);
			assertNull(randomIndex.get(key));
		}
		
		time = System.currentTimeMillis() - time;
		System.err.println("randomTest time: " + time + " ms");
	}
}
