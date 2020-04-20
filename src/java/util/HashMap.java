/*
 * Copyright (c) 1997, 2010, Oracle and/or its affiliates. All rights reserved. ORACLE PROPRIETARY/CONFIDENTIAL. Use is
 * subject to license terms.
 */

package java.util;

import java.io.*;

/**
 * Hash table based implementation of the <tt>Map</tt> interface. This implementation provides all of the optional map
 * operations, and permits <tt>null</tt> values and the <tt>null</tt> key. (The <tt>HashMap</tt> class is roughly
 * equivalent to <tt>Hashtable</tt>, except that it is unsynchronized and permits nulls.) This class makes no guarantees
 * as to the order of the map; in particular, it does not guarantee that the order will remain constant over time.
 * <p>
 * This implementation provides constant-time performance for the basic operations (<tt>get</tt> and <tt>put</tt>),
 * assuming the hash function disperses the elements properly among the buckets. Iteration over collection views
 * requires time proportional to the "capacity" of the <tt>HashMap</tt> instance (the number of buckets) plus its size
 * (the number of key-value mappings). Thus, it's very important not to set the initial capacity too high (or the load
 * factor too low) if iteration performance is important.
 * <p>
 * An instance of <tt>HashMap</tt> has two parameters that affect its performance: <i>initial capacity</i> and <i>load
 * factor</i>. The <i>capacity</i> is the number of buckets in the hash table, and the initial capacity is simply the
 * capacity at the time the hash table is created. The <i>load factor</i> is a measure of how full the hash table is
 * allowed to get before its capacity is automatically increased. When the number of entries in the hash table exceeds
 * the product of the load factor and the current capacity, the hash table is <i>rehashed</i> (that is, internal data
 * structures are rebuilt) so that the hash table has approximately twice the number of buckets.
 * <p>
 * As a general rule, the default load factor (.75) offers a good tradeoff between time and space costs. Higher values
 * decrease the space overhead but increase the lookup cost (reflected in most of the operations of the <tt>HashMap</tt>
 * class, including <tt>get</tt> and <tt>put</tt>). The expected number of entries in the map and its load factor should
 * be taken into account when setting its initial capacity, so as to minimize the number of rehash operations. If the
 * initial capacity is greater than the maximum number of entries divided by the load factor, no rehash operations will
 * ever occur.
 * <p>
 * If many mappings are to be stored in a <tt>HashMap</tt> instance, creating it with a sufficiently large capacity will
 * allow the mappings to be stored more efficiently than letting it perform automatic rehashing as needed to grow the
 * table.
 * <p>
 * <strong>Note that this implementation is not synchronized.</strong> If multiple threads access a hash map
 * concurrently, and at least one of the threads modifies the map structurally, it <i>must</i> be synchronized
 * externally. (A structural modification is any operation that adds or deletes one or more mappings; merely changing
 * the value associated with a key that an instance already contains is not a structural modification.) This is
 * typically accomplished by synchronizing on some object that naturally encapsulates the map. If no such object exists,
 * the map should be "wrapped" using the {@link Collections#synchronizedMap Collections.synchronizedMap} method. This is
 * best done at creation time, to prevent accidental unsynchronized access to the map:
 * 
 * <pre>
 *   Map m = Collections.synchronizedMap(new HashMap(...));
 * </pre>
 * <p>
 * The iterators returned by all of this class's "collection view methods" are <i>fail-fast</i>: if the map is
 * structurally modified at any time after the iterator is created, in any way except through the iterator's own
 * <tt>remove</tt> method, the iterator will throw a {@link ConcurrentModificationException}. Thus, in the face of
 * concurrent modification, the iterator fails quickly and cleanly, rather than risking arbitrary, non-deterministic
 * behavior at an undetermined time in the future.
 * <p>
 * Note that the fail-fast behavior of an iterator cannot be guaranteed as it is, generally speaking, impossible to make
 * any hard guarantees in the presence of unsynchronized concurrent modification. Fail-fast iterators throw
 * <tt>ConcurrentModificationException</tt> on a best-effort basis. Therefore, it would be wrong to write a program that
 * depended on this exception for its correctness: <i>the fail-fast behavior of iterators should be used only to detect
 * bugs.</i>
 * <p>
 * This class is a member of the <a href="{@docRoot}/../technotes/guides/collections/index.html"> Java Collections
 * Framework</a>.
 *
 * @param <K>
 *            the type of keys maintained by this map
 * @param <V>
 *            the type of mapped values
 * @author Doug Lea
 * @author Josh Bloch
 * @author Arthur van Hoff
 * @author Neal Gafter
 * @see Object#hashCode()
 * @see Collection
 * @see Map
 * @see TreeMap
 * @see Hashtable
 * @since 1.2
 */

public class HashMap<K, V> extends AbstractMap<K, V> implements Map<K, V>, Cloneable, Serializable
{

	/**
	 * The default initial capacity - MUST be a power of two.
	 */
	// 默认的初始容量是16，必须是2的幂。
	static final int DEFAULT_INITIAL_CAPACITY = 1 << 4; // 16

	/**
	 * The maximum capacity, used if a higher value is implicitly specified by either of the constructors with
	 * arguments. MUST be a power of two <= 1<<30.
	 */
	// 最大容量（必须是2的幂且小于2的30次方，传入容量过大将被这个值替换）
	static final int MAXIMUM_CAPACITY = 1 << 30;

	/**
	 * The load factor used when none specified in constructor.
	 */
	// 默认加载因子
	static final float DEFAULT_LOAD_FACTOR = 0.75f;

	/**
	 * An empty table instance to share when the table is not inflated.
	 */
	static final Entry<?, ?>[] EMPTY_TABLE = {};

	/**
	 * The table, resized as necessary. Length MUST Always be a power of two.
	 */
	// 存储数据的Entry数组，长度是2的幂。
	// HashMap是采用拉链法实现的，每一个Entry本质上是一个单向链表
	transient Entry<K, V>[] table = (Entry<K, V>[]) EMPTY_TABLE;

	/**
	 * The number of key-value mappings contained in this map.
	 */
	// HashMap的大小，它是HashMap保存的键值对的数量
	transient int size;

	/**
	 * The next size value at which to resize (capacity * load factor).
	 * 
	 * @serial
	 */
	// If table == EMPTY_TABLE then this is the initial capacity at which the
	// table will be created when inflated.
	// HashMap的阈值，用于判断是否需要调整HashMap的容量（threshold = 容量*加载因子）
	int threshold;

	/**
	 * The load factor for the hash table.
	 *
	 * @serial
	 */
	// 加载因子实际大小
	final float loadFactor;

	/**
	 * The number of times this HashMap has been structurally modified Structural modifications are those that change
	 * the number of mappings in the HashMap or otherwise modify its internal structure (e.g., rehash). This field is
	 * used to make iterators on Collection-views of the HashMap fail-fast. (See ConcurrentModificationException).
	 */
	// HashMap被改变的次数
	transient int modCount;

	/**
	 * The default threshold of map capacity above which alternative hashing is used for String keys. Alternative
	 * hashing reduces the incidence of collisions due to weak hash code calculation for String keys.
	 * <p/>
	 * This value may be overridden by defining the system property {@code jdk.map.althashing.threshold}. A property
	 * value of {@code 1} forces alternative hashing to be used at all times whereas {@code -1} value ensures that
	 * alternative hashing is never used.
	 */
	static final int ALTERNATIVE_HASHING_THRESHOLD_DEFAULT = Integer.MAX_VALUE;

	/**
	 * holds values which can't be initialized until after VM is booted.
	 */
	private static class Holder
	{

		/**
		 * Table capacity above which to switch to use alternative hashing.
		 */
		static final int ALTERNATIVE_HASHING_THRESHOLD;

		static
		{
			String altThreshold = java.security.AccessController
					.doPrivileged(new sun.security.action.GetPropertyAction("jdk.map.althashing.threshold"));

			int threshold;
			try
			{
				threshold = (null != altThreshold) ? Integer.parseInt(altThreshold)
						: ALTERNATIVE_HASHING_THRESHOLD_DEFAULT;

				// disable alternative hashing if -1
				if (threshold == -1)
				{
					threshold = Integer.MAX_VALUE;
				}

				if (threshold < 0)
				{
					throw new IllegalArgumentException("value must be positive integer.");
				}
			}
			catch (IllegalArgumentException failed)
			{
				throw new Error("Illegal value for 'jdk.map.althashing.threshold'", failed);
			}

			ALTERNATIVE_HASHING_THRESHOLD = threshold;
		}
	}

	/**
	 * A randomizing value associated with this instance that is applied to hash code of keys to make hash collisions
	 * harder to find. If 0 then alternative hashing is disabled.
	 */
	transient int hashSeed = 0;

	/**
	 * Constructs an empty <tt>HashMap</tt> with the specified initial capacity and load factor.
	 *
	 * @param initialCapacity
	 *            the initial capacity
	 * @param loadFactor
	 *            the load factor
	 * @throws IllegalArgumentException
	 *             if the initial capacity is negative or the load factor is nonpositive
	 */
	// 指定“容量大小”和“加载因子”的构造函数
	public HashMap(int initialCapacity, float loadFactor)
	{
		if (initialCapacity < 0)
			throw new IllegalArgumentException("Illegal initial capacity: " + initialCapacity);
		// HashMap的最大容量只能是MAXIMUM_CAPACITY
		if (initialCapacity > MAXIMUM_CAPACITY)
			initialCapacity = MAXIMUM_CAPACITY;
		if (loadFactor <= 0 || Float.isNaN(loadFactor))
			throw new IllegalArgumentException("Illegal load factor: " + loadFactor);

		// 设置“加载因子”
		this.loadFactor = loadFactor;
		// 设置“HashMap阈值”，当HashMap中存储数据的数量达到threshold时，就需要将HashMap的容量加倍。
		threshold = initialCapacity;
		init();
	}

	/**
	 * Constructs an empty <tt>HashMap</tt> with the specified initial capacity and the default load factor (0.75).
	 *
	 * @param initialCapacity
	 *            the initial capacity.
	 * @throws IllegalArgumentException
	 *             if the initial capacity is negative.
	 */
	public HashMap(int initialCapacity)
	{
		this(initialCapacity, DEFAULT_LOAD_FACTOR);
	}

	/**
	 * Constructs an empty <tt>HashMap</tt> with the default initial capacity (16) and the default load factor (0.75).
	 */
	public HashMap()
	{
		this(DEFAULT_INITIAL_CAPACITY, DEFAULT_LOAD_FACTOR);
	}

	/**
	 * Constructs a new <tt>HashMap</tt> with the same mappings as the specified <tt>Map</tt>. The <tt>HashMap</tt> is
	 * created with default load factor (0.75) and an initial capacity sufficient to hold the mappings in the specified
	 * <tt>Map</tt>.
	 *
	 * @param m
	 *            the map whose mappings are to be placed in this map
	 * @throws NullPointerException
	 *             if the specified map is null
	 */
	// 包含“子Map”的构造函数
	public HashMap(Map<? extends K, ? extends V> m)
	{
		this(Math.max((int) (m.size() / DEFAULT_LOAD_FACTOR) + 1, DEFAULT_INITIAL_CAPACITY), DEFAULT_LOAD_FACTOR);
		inflateTable(threshold);

		// 将m中的全部元素逐个添加到HashMap中
		putAllForCreate(m);
	}

	// 把number的设置成2的n次方
	private static int roundUpToPowerOf2(int number)
	{
		// assert number >= 0 : "number must be non-negative";
		return number >= MAXIMUM_CAPACITY ? MAXIMUM_CAPACITY
				: (number > 1) ? Integer.highestOneBit((number - 1) << 1) : 1;
	}

	/**
	 * Inflates the table.
	 */
	private void inflateTable(int toSize)
	{
		// Find a power of 2 >= toSize
		// 为了减少hash冲突，最好把数组设置成2的n次方，此方法用于找到大于toSize的“最小的2的n次方”
		int capacity = roundUpToPowerOf2(toSize);

		threshold = (int) Math.min(capacity * loadFactor, MAXIMUM_CAPACITY + 1);
		table = new Entry[capacity];
		initHashSeedAsNeeded(capacity);
	}

	// internal utilities

	/**
	 * Initialization hook for subclasses. This method is called in all constructors and pseudo-constructors (clone,
	 * readObject) after HashMap has been initialized but before any entries have been inserted. (In the absence of this
	 * method, readObject would require explicit knowledge of subclasses.)
	 */
	void init()
	{
	}

	/**
	 * Initialize the hashing mask value. We defer initialization until we really need it.
	 */
	final boolean initHashSeedAsNeeded(int capacity)
	{
		boolean currentAltHashing = hashSeed != 0;
		boolean useAltHashing = sun.misc.VM.isBooted() && (capacity >= Holder.ALTERNATIVE_HASHING_THRESHOLD);
		boolean switching = currentAltHashing ^ useAltHashing;
		if (switching)
		{
			hashSeed = useAltHashing ? sun.misc.Hashing.randomHashSeed(this) : 0;
		}
		return switching;
	}

	/**
	 * Retrieve object hash code and applies a supplemental hash function to the result hash, which defends against poor
	 * quality hash functions. This is critical because HashMap uses power-of-two length hash tables, that otherwise
	 * encounter collisions for hashCodes that do not differ in lower bits. Note: Null keys always map to hash 0, thus
	 * index 0.
	 */
	final int hash(Object k)
	{
		int h = hashSeed;
		if (0 != h && k instanceof String)
		{
			return sun.misc.Hashing.stringHash32((String) k);
		}

		h ^= k.hashCode();

		// This function ensures that hashCodes that differ only by
		// constant multiples at each bit position have a bounded
		// number of collisions (approximately 8 at default load factor).
		h ^= (h >>> 20) ^ (h >>> 12);
		return h ^ (h >>> 7) ^ (h >>> 4);
	}

	// 使用位操作（&运算）代替求余操作
	// %运算:a%b
	// 由于我们知道位运算比较高效，当b为2的n次方时，有如下替换公式：
	// a % b = a & (b-1)(b=2n)
	// 即：a % 2n = a & (2n-1)
	// 例如：14%8，取余数，相当于取出低位，而余数最大为7，14二进制为1110，8的二进制1000，
	// 8-1 = 7的二进制为0111，由于现在低位全为1，让其跟14做&运算，正好取出的是其低位上的余数。
	// 1110&0111=110即6=14%8；
	// （此公式只适用b=2n，是因为可以保证b始终只有最高位为1，其他二进制位全部为0，减去1，之后，
	// 可以把高位1消除，其他位都为1，而与1做&运算，会保留原来的数。）
	/**
	 * Returns index for hash code h. <br/>
	 * 利用Key的hash值和数组的长度（length），找到key对应在table数组中的下标 <br/>
	 * 原理：位运算比较高效；当b为2的n次方时，有如下替换公式： <br/>
	 * a % b = a & (b-1)(b=2^n) 即：a % 2n = a & (2^n-1)
	 * 
	 * @param h
	 *            key的hash值
	 * @param length
	 *            HashMap中table数组的长度
	 * @return 下标
	 */
	static int indexFor(int h, int length)
	{
		// assert Integer.bitCount(length) == 1 : "length must be a non-zero power of 2";
		// 以下操作实际上相当于h%length取余数，但&计算速度更快
		return h & (length - 1);
	}

	/**
	 * Returns the number of key-value mappings in this map.
	 *
	 * @return the number of key-value mappings in this map
	 */
	public int size()
	{
		return size;
	}

	/**
	 * Returns <tt>true</tt> if this map contains no key-value mappings.
	 *
	 * @return <tt>true</tt> if this map contains no key-value mappings
	 */
	public boolean isEmpty()
	{
		return size == 0;
	}

	/**
	 * Returns the value to which the specified key is mapped, or {@code null} if this map contains no mapping for the
	 * key.
	 * <p>
	 * More formally, if this map contains a mapping from a key {@code k} to a value {@code v} such that
	 * {@code (key==null ? k==null :
	 * key.equals(k))}, then this method returns {@code v}; otherwise it returns {@code null}. (There can be at most one
	 * such mapping.)
	 * <p>
	 * A return value of {@code null} does not <i>necessarily</i> indicate that the map contains no mapping for the key;
	 * it's also possible that the map explicitly maps the key to {@code null}. The {@link #containsKey containsKey}
	 * operation may be used to distinguish these two cases.
	 *
	 * @see #put(Object, Object)
	 */
	// 获取key对应的value
	public V get(Object key)
	{
		if (key == null)
			return getForNullKey();
		Entry<K, V> entry = getEntry(key);

		return null == entry ? null : entry.getValue();
	}

	/**
	 * Offloaded version of get() to look up null keys. Null keys map to index 0. This null case is split out into
	 * separate methods for the sake of performance in the two most commonly used operations (get and put), but
	 * incorporated with conditionals in others.
	 */
	// 获取“key为null”的元素的值
	// HashMap将“key为null”的元素存储在table[0]位置！
	private V getForNullKey()
	{
		if (size == 0)
		{
			return null;
		}
		for (Entry<K, V> e = table[0]; e != null; e = e.next)
		{
			if (e.key == null)
				return e.value;
		}
		return null;
	}

	/**
	 * Returns <tt>true</tt> if this map contains a mapping for the specified key.
	 *
	 * @param key
	 *            The key whose presence in this map is to be tested
	 * @return <tt>true</tt> if this map contains a mapping for the specified key.
	 */
	// HashMap是否包含key
	public boolean containsKey(Object key)
	{
		return getEntry(key) != null;
	}

	/**
	 * Returns the entry associated with the specified key in the HashMap. Returns null if the HashMap contains no
	 * mapping for the key.
	 */
	// 返回“键为key”的键值对
	final Entry<K, V> getEntry(Object key)
	{
		if (size == 0)
		{
			return null;
		}

		// 获取key的hash值
		// HashMap将“key为null”的元素存储在table[0]位置，“key不为null”的则调用hash()计算哈希值
		int hash = (key == null) ? 0 : hash(key);
		// 在“该hash值对应的链表”上查找“键值等于key”的元素
		for (Entry<K, V> e = table[indexFor(hash, table.length)]; e != null; e = e.next)
		{
			Object k;
			if (e.hash == hash && ((k = e.key) == key || (key != null && key.equals(k))))
				return e;
		}
		return null;
	}

	/**
	 * Associates the specified value with the specified key in this map. If the map previously contained a mapping for
	 * the key, the old value is replaced.
	 *
	 * @param key
	 *            key with which the specified value is to be associated
	 * @param value
	 *            value to be associated with the specified key
	 * @return the previous value associated with <tt>key</tt>, or <tt>null</tt> if there was no mapping for
	 *         <tt>key</tt>. (A <tt>null</tt> return can also indicate that the map previously associated <tt>null</tt>
	 *         with <tt>key</tt>.)
	 */
	// 将“key-value”添加到HashMap中
	public V put(K key, V value)
	{
		if (table == EMPTY_TABLE)
		{
			inflateTable(threshold);
		}
		// 若“key为null”，则将该键值对添加到table[0]中。
		if (key == null)
			return putForNullKey(value);
		int hash = hash(key);
		int i = indexFor(hash, table.length);
		for (Entry<K, V> e = table[i]; e != null; e = e.next)
		{
			Object k;
			// 若“该key”对应的键值对已经存在，则用新的value取代旧的value。然后退出！
			if (e.hash == hash && ((k = e.key) == key || key.equals(k)))
			{
				V oldValue = e.value;
				e.value = value;
				e.recordAccess(this);
				return oldValue;
			}
		}

		// 若“该key”对应的键值对不存在，则将“key-value”添加到table中
		modCount++;
		addEntry(hash, key, value, i);
		return null;
	}

	/**
	 * Offloaded version of put for null keys
	 */
	// putForNullKey()的作用是将“key为null”键值对添加到table[0]位置
	private V putForNullKey(V value)
	{
		for (Entry<K, V> e = table[0]; e != null; e = e.next)
		{
			if (e.key == null)
			{
				V oldValue = e.value;
				e.value = value;
				e.recordAccess(this);
				return oldValue;
			}
		}
		// 这里的完全不会被执行到!
		modCount++;
		addEntry(0, null, value, 0);
		return null;
	}

	/**
	 * This method is used instead of put by constructors and pseudoconstructors (clone, readObject). It does not resize
	 * the table, check for comodification, etc. It calls createEntry rather than addEntry.
	 */
	// 创建HashMap对应的“添加方法”，
	// 它和put()不同。putForCreate()是内部方法，它被构造函数等调用，用来创建HashMap
	// 而put()是对外提供的往HashMap中添加元素的方法。
	private void putForCreate(K key, V value)
	{
		int hash = null == key ? 0 : hash(key);
		int i = indexFor(hash, table.length);

		/**
		 * Look for preexisting entry for key. This will never happen for clone or deserialize. It will only happen for
		 * construction if the input Map is a sorted map whose ordering is inconsistent w/ equals.
		 */
		// 若该HashMap表中存在“键值等于key”的元素，则替换该元素的value值
		for (Entry<K, V> e = table[i]; e != null; e = e.next)
		{
			Object k;
			if (e.hash == hash && ((k = e.key) == key || (key != null && key.equals(k))))
			{
				e.value = value;
				return;
			}
		}
		// 若该HashMap表中不存在“键值等于key”的元素，则将该key-value添加到HashMap中
		createEntry(hash, key, value, i);
	}

	// 将“m”中的全部元素都添加到HashMap中。
	// 该方法被内部的构造HashMap的方法所调用。
	private void putAllForCreate(Map<? extends K, ? extends V> m)
	{
		for (Map.Entry<? extends K, ? extends V> e : m.entrySet())
			putForCreate(e.getKey(), e.getValue());
	}

	/**
	 * Rehashes the contents of this map into a new array with a larger capacity. This method is called automatically
	 * when the number of keys in this map reaches its threshold. If current capacity is MAXIMUM_CAPACITY, this method
	 * does not resize the map, but sets threshold to Integer.MAX_VALUE. This has the effect of preventing future calls.
	 *
	 * @param newCapacity
	 *            the new capacity, MUST be a power of two; must be greater than current capacity unless current
	 *            capacity is MAXIMUM_CAPACITY (in which case value is irrelevant).
	 */
	// 重新调整HashMap的大小，newCapacity是调整后的单位
	void resize(int newCapacity)
	{
		Entry[] oldTable = table;
		int oldCapacity = oldTable.length;
		if (oldCapacity == MAXIMUM_CAPACITY)
		{
			threshold = Integer.MAX_VALUE;
			return;
		}

		// 新建一个HashMap，将“旧HashMap”的全部元素添加到“新HashMap”中，
		// 然后，将“新HashMap”赋值给“旧HashMap”。
		Entry[] newTable = new Entry[newCapacity];
		transfer(newTable, initHashSeedAsNeeded(newCapacity));
		table = newTable;
		threshold = (int) Math.min(newCapacity * loadFactor, MAXIMUM_CAPACITY + 1);
	}

	/**
	 * Transfers all entries from current table to newTable.
	 */
	// 将HashMap中的全部元素都添加到newTable中
	void transfer(Entry[] newTable, boolean rehash)
	{
		int newCapacity = newTable.length;
		for (Entry<K, V> e : table)
		{
			while (null != e)
			{
				Entry<K, V> next = e.next;
				if (rehash)
				{
					e.hash = null == e.key ? 0 : hash(e.key);
				}
				int i = indexFor(e.hash, newCapacity);
				e.next = newTable[i];
				newTable[i] = e;
				e = next;
			}
		}
	}

	/**
	 * Copies all of the mappings from the specified map to this map. These mappings will replace any mappings that this
	 * map had for any of the keys currently in the specified map.
	 *
	 * @param m
	 *            mappings to be stored in this map
	 * @throws NullPointerException
	 *             if the specified map is null
	 */
	// 将"m"的全部元素都添加到HashMap中
	public void putAll(Map<? extends K, ? extends V> m)
	{
		// 有效性判断
		int numKeysToBeAdded = m.size();
		if (numKeysToBeAdded == 0)
			return;

		if (table == EMPTY_TABLE)
		{
			inflateTable((int) Math.max(numKeysToBeAdded * loadFactor, threshold));
		}

		/*
		 * Expand the map if the map if the number of mappings to be added is greater than or equal to threshold. This
		 * is conservative; the obvious condition is (m.size() + size) >= threshold, but this condition could result in
		 * a map with twice the appropriate capacity, if the keys to be added overlap with the keys already in this map.
		 * By using the conservative calculation, we subject ourself to at most one extra resize.
		 */
		// 计算容量是否足够，
		// 若“当前实际容量 < 需要的容量”，则将容量x2。
		if (numKeysToBeAdded > threshold)
		{
			int targetCapacity = (int) (numKeysToBeAdded / loadFactor + 1);
			if (targetCapacity > MAXIMUM_CAPACITY)
				targetCapacity = MAXIMUM_CAPACITY;
			int newCapacity = table.length;
			while (newCapacity < targetCapacity)
				newCapacity <<= 1;
			if (newCapacity > table.length)
				resize(newCapacity);
		}
		// 将“m”中的元素逐个添加到HashMap中。
		for (Map.Entry<? extends K, ? extends V> e : m.entrySet())
			put(e.getKey(), e.getValue());
	}

	/**
	 * Removes the mapping for the specified key from this map if present.
	 *
	 * @param key
	 *            key whose mapping is to be removed from the map
	 * @return the previous value associated with <tt>key</tt>, or <tt>null</tt> if there was no mapping for
	 *         <tt>key</tt>. (A <tt>null</tt> return can also indicate that the map previously associated <tt>null</tt>
	 *         with <tt>key</tt>.)
	 */
	// 删除“键为key”元素
	public V remove(Object key)
	{
		Entry<K, V> e = removeEntryForKey(key);
		return (e == null ? null : e.value);
	}

	/**
	 * Removes and returns the entry associated with the specified key in the HashMap. Returns null if the HashMap
	 * contains no mapping for this key.
	 */
	// 删除“键为key”的元素
	final Entry<K, V> removeEntryForKey(Object key)
	{
		if (size == 0)
		{
			return null;
		}
		// 获取哈希值。若key为null，则哈希值为0；否则调用hash()进行计算
		int hash = (key == null) ? 0 : hash(key);
		int i = indexFor(hash, table.length);
		Entry<K, V> prev = table[i];
		Entry<K, V> e = prev;

		// 删除链表中“键为key”的元素
		// 本质是“删除单向链表中的节点”
		while (e != null)
		{
			Entry<K, V> next = e.next;
			Object k;
			if (e.hash == hash && ((k = e.key) == key || (key != null && key.equals(k))))
			{
				modCount++;
				size--;
				if (prev == e)
					table[i] = next;
				else
					prev.next = next;
				e.recordRemoval(this);
				return e;
			}
			prev = e;
			e = next;
		}

		return e;
	}

	/**
	 * Special version of remove for EntrySet using {@code Map.Entry.equals()} for matching.
	 */
	// 删除“键值对”
	final Entry<K, V> removeMapping(Object o)
	{
		if (size == 0 || !(o instanceof Map.Entry))
			return null;

		Map.Entry<K, V> entry = (Map.Entry<K, V>) o;
		Object key = entry.getKey();
		int hash = (key == null) ? 0 : hash(key);
		int i = indexFor(hash, table.length);
		Entry<K, V> prev = table[i];
		Entry<K, V> e = prev;

		// 删除链表中的“键值对e”
		// 本质是“删除单向链表中的节点”
		while (e != null)
		{
			Entry<K, V> next = e.next;
			if (e.hash == hash && e.equals(entry))
			{
				modCount++;
				size--;
				if (prev == e)
					table[i] = next;
				else
					prev.next = next;
				e.recordRemoval(this);
				return e;
			}
			prev = e;
			e = next;
		}

		return e;
	}

	/**
	 * Removes all of the mappings from this map. The map will be empty after this call returns.
	 */
	// 清空HashMap，将所有的元素设为null
	public void clear()
	{
		modCount++;
		Arrays.fill(table, null);
		size = 0;
	}

	/**
	 * Returns <tt>true</tt> if this map maps one or more keys to the specified value.
	 *
	 * @param value
	 *            value whose presence in this map is to be tested
	 * @return <tt>true</tt> if this map maps one or more keys to the specified value
	 */
	// 是否包含“值为value”的元素
	public boolean containsValue(Object value)
	{
		// 若“value为null”，则调用containsNullValue()查找
		if (value == null)
			return containsNullValue();

		// 若“value不为null”，则查找HashMap中是否有值为value的节点。
		Entry[] tab = table;
		for (int i = 0; i < tab.length; i++)
			for (Entry e = tab[i]; e != null; e = e.next)
				if (value.equals(e.value))
					return true;
		return false;
	}

	/**
	 * Special-case code for containsValue with null argument
	 */
	// 是否包含null值
	private boolean containsNullValue()
	{
		Entry[] tab = table;
		for (int i = 0; i < tab.length; i++)
			for (Entry e = tab[i]; e != null; e = e.next)
				if (e.value == null)
					return true;
		return false;
	}

	/**
	 * Returns a shallow copy of this <tt>HashMap</tt> instance: the keys and values themselves are not cloned.
	 *
	 * @return a shallow copy of this map
	 */
	// 克隆一个HashMap，并返回Object对象
	public Object clone()
	{
		HashMap<K, V> result = null;
		try
		{
			result = (HashMap<K, V>) super.clone();
		}
		catch (CloneNotSupportedException e)
		{
			// assert false;
		}
		if (result.table != EMPTY_TABLE)
		{
			result.inflateTable(Math.min((int) Math.min(size * Math.min(1 / loadFactor, 4.0f),
					// we have limits...
					HashMap.MAXIMUM_CAPACITY), table.length));
		}
		result.entrySet = null;
		result.modCount = 0;
		result.size = 0;
		result.init();
		// 调用putAllForCreate()将全部元素添加到HashMap中
		result.putAllForCreate(this);

		return result;
	}

	// Entry是单向链表。
	// 它是 “HashMap链式存储法”对应的链表。
	// 它实现了Map.Entry 接口，即实现getKey(), getValue(), setValue(V value), equals(Object o), hashCode()这些函数
	static class Entry<K, V> implements Map.Entry<K, V>
	{
		final K key;
		V value;
		// 指向下一个节点
		Entry<K, V> next;
		int hash;

		/**
		 * Creates new entry.
		 */
		// 构造函数。
		// 输入参数包括"哈希值(h)", "键(k)", "值(v)", "下一节点
		Entry(int h, K k, V v, Entry<K, V> n)
		{
			value = v;
			next = n;
			key = k;
			hash = h;
		}

		public final K getKey()
		{
			return key;
		}

		public final V getValue()
		{
			return value;
		}

		public final V setValue(V newValue)
		{
			V oldValue = value;
			value = newValue;
			return oldValue;
		}

		// 判断两个Entry是否相等
		// 若两个Entry的“key”和“value”都相等，则返回true。
		// 否则，返回false
		public final boolean equals(Object o)
		{
			if (!(o instanceof Map.Entry))
				return false;
			Map.Entry e = (Map.Entry) o;
			Object k1 = getKey();
			Object k2 = e.getKey();
			if (k1 == k2 || (k1 != null && k1.equals(k2)))
			{
				Object v1 = getValue();
				Object v2 = e.getValue();
				if (v1 == v2 || (v1 != null && v1.equals(v2)))
					return true;
			}
			return false;
		}

		// 实现hashCode()
		public final int hashCode()
		{
			return Objects.hashCode(getKey()) ^ Objects.hashCode(getValue());
		}

		public final String toString()
		{
			return getKey() + "=" + getValue();
		}

		/**
		 * This method is invoked whenever the value in an entry is overwritten by an invocation of put(k,v) for a key k
		 * that's already in the HashMap.
		 */
		// 当向HashMap中添加元素时，绘调用recordAccess()。
		// 这里不做任何处理
		void recordAccess(HashMap<K, V> m)
		{
		}

		/**
		 * This method is invoked whenever the entry is removed from the table.
		 */
		// 当从HashMap中删除元素时，绘调用recordRemoval()。
		// 这里不做任何处理
		void recordRemoval(HashMap<K, V> m)
		{
		}
	}

	/**
	 * Adds a new entry with the specified key, value and hash code to the specified bucket. It is the responsibility of
	 * this method to resize the table if appropriate. Subclass overrides this to alter the behavior of put method.
	 */
	// 新增Entry。将“key-value”插入指定位置，bucketIndex是位置索
	void addEntry(int hash, K key, V value, int bucketIndex)
	{
		// 若HashMap的实际大小 不小于 “阈值”，则调整HashMap的大小
		if ((size >= threshold) && (null != table[bucketIndex]))
		{
			resize(2 * table.length);
			hash = (null != key) ? hash(key) : 0;
			bucketIndex = indexFor(hash, table.length);
		}

		createEntry(hash, key, value, bucketIndex);
	}

	/**
	 * Like addEntry except that this version is used when creating entries as part of Map construction or
	 * "pseudo-construction" (cloning, deserialization). This version needn't worry about resizing the table. Subclass
	 * overrides this to alter the behavior of HashMap(Map), clone, and readObject.
	 */
	// 创建Entry。将“key-value”插入指定位置，bucketIndex是位置索引。
	// 它和addEntry的区别是：
	// (01) addEntry()一般用在 新增Entry可能导致“HashMap的实际容量”超过“阈值”的情况下。
	// 例如，我们新建一个HashMap，然后不断通过put()向HashMap中添加元素；
	// put()是通过addEntry()新增Entry的。
	// 在这种情况下，我们不知道何时“HashMap的实际容量”会超过“阈值”；
	// 因此，需要调用addEntry()
	// (02) createEntry() 一般用在 新增Entry不会导致“HashMap的实际容量”超过“阈值”的情况下。
	// 例如，我们调用HashMap“带有Map”的构造函数，它绘将Map的全部元素添加到HashMap中；
	// 但在添加之前，我们已经计算好“HashMap的容量和阈值”。也就是，可以确定“即使将Map中
	// 的全部元素添加到HashMap中，都不会超过HashMap的阈值”。
	// 此时，调用createEntry()即可。
	void createEntry(int hash, K key, V value, int bucketIndex)
	{
		// 保存“bucketIndex”位置的值到“e”中
		Entry<K, V> e = table[bucketIndex];
		// 设置“bucketIndex”位置的元素为“新Entry”，
		// 设置“e”为“新Entry的下一个节点”
		table[bucketIndex] = new Entry<>(hash, key, value, e);
		size++;
	}

	// HashIterator是HashMap迭代器的抽象出来的父类，实现了公共了函数。
	// 它包含“key迭代器(KeyIterator)”、“Value迭代器(ValueIterator)”和“Entry迭代器(EntryIterator)”3个子类。
	private abstract class HashIterator<E> implements Iterator<E>
	{
		// 下一个元素
		Entry<K, V> next;        // next entry to return
		// expectedModCount用于实现fast-fail机制。
		int expectedModCount;   // For fast-fail
		// 当前索引
		int index;              // current slot
		// 当前元素
		Entry<K, V> current;     // current entry

		HashIterator()
		{
			expectedModCount = modCount;
			if (size > 0)
			{ // advance to first entry
				Entry[] t = table;
				// 将next指向table中第一个不为null的元素。
				// 这里利用了index的初始值为0，从0开始依次向后遍历，直到找到不为null的元素就退出循环。
				while (index < t.length && (next = t[index++]) == null)
					;
			}
		}

		public final boolean hasNext()
		{
			return next != null;
		}

		// 获取下一个元素
		final Entry<K, V> nextEntry()
		{
			if (modCount != expectedModCount)
				throw new ConcurrentModificationException();
			Entry<K, V> e = next;
			if (e == null)
				throw new NoSuchElementException();

			// 注意！！！
			// 一个Entry就是一个单向链表
			// 若该Entry的下一个节点不为空，就将next指向下一个节点;
			// 否则，将next指向下一个链表(也是下一个Entry)的不为null的节点。
			if ((next = e.next) == null)
			{
				Entry[] t = table;
				while (index < t.length && (next = t[index++]) == null)
					;
			}
			current = e;
			return e;
		}

		// 删除当前元素
		public void remove()
		{
			if (current == null)
				throw new IllegalStateException();
			if (modCount != expectedModCount)
				throw new ConcurrentModificationException();
			Object k = current.key;
			current = null;
			HashMap.this.removeEntryForKey(k);
			expectedModCount = modCount;
		}
	}

	// value的迭代器
	private final class ValueIterator extends HashIterator<V>
	{
		public V next()
		{
			return nextEntry().value;
		}
	}

	// key的迭代器
	private final class KeyIterator extends HashIterator<K>
	{
		public K next()
		{
			return nextEntry().getKey();
		}
	}

	// Entry的迭代器
	private final class EntryIterator extends HashIterator<Map.Entry<K, V>>
	{
		public Map.Entry<K, V> next()
		{
			return nextEntry();
		}
	}

	// Subclass overrides these to alter behavior of views' iterator() method
	Iterator<K> newKeyIterator()
	{
		return new KeyIterator();
	}

	Iterator<V> newValueIterator()
	{
		return new ValueIterator();
	}

	Iterator<Map.Entry<K, V>> newEntryIterator()
	{
		return new EntryIterator();
	}

	// Views
	// HashMap的Entry对应的集合
	private transient Set<Map.Entry<K, V>> entrySet = null;

	/**
	 * Returns a {@link Set} view of the keys contained in this map. The set is backed by the map, so changes to the map
	 * are reflected in the set, and vice-versa. If the map is modified while an iteration over the set is in progress
	 * (except through the iterator's own <tt>remove</tt> operation), the results of the iteration are undefined. The
	 * set supports element removal, which removes the corresponding mapping from the map, via the
	 * <tt>Iterator.remove</tt>, <tt>Set.remove</tt>, <tt>removeAll</tt>, <tt>retainAll</tt>, and <tt>clear</tt>
	 * operations. It does not support the <tt>add</tt> or <tt>addAll</tt> operations.
	 */
	// 返回“key的集合”，实际上返回一个“KeySet对象”
	public Set<K> keySet()
	{
		Set<K> ks = keySet;
		return (ks != null ? ks : (keySet = new KeySet()));
	}

	// Key对应的集合
	// KeySet继承于AbstractSet，说明该集合中没有重复的Key。
	private final class KeySet extends AbstractSet<K>
	{
		public Iterator<K> iterator()
		{
			return newKeyIterator();
		}

		public int size()
		{
			return size;
		}

		public boolean contains(Object o)
		{
			return containsKey(o);
		}

		public boolean remove(Object o)
		{
			return HashMap.this.removeEntryForKey(o) != null;
		}

		public void clear()
		{
			HashMap.this.clear();
		}
	}

	/**
	 * Returns a {@link Collection} view of the values contained in this map. The collection is backed by the map, so
	 * changes to the map are reflected in the collection, and vice-versa. If the map is modified while an iteration
	 * over the collection is in progress (except through the iterator's own <tt>remove</tt> operation), the results of
	 * the iteration are undefined. The collection supports element removal, which removes the corresponding mapping
	 * from the map, via the <tt>Iterator.remove</tt>, <tt>Collection.remove</tt>, <tt>removeAll</tt>,
	 * <tt>retainAll</tt> and <tt>clear</tt> operations. It does not support the <tt>add</tt> or <tt>addAll</tt>
	 * operations.
	 */
	// 返回“value集合”，实际上返回的是一个Values对象
	public Collection<V> values()
	{
		Collection<V> vs = values;
		return (vs != null ? vs : (values = new Values()));
	}

	// “value集合”
	// Values继承于AbstractCollection，不同于“KeySet继承于AbstractSet”，
	// Values中的元素能够重复。因为不同的key可以指向相同的value。
	private final class Values extends AbstractCollection<V>
	{
		public Iterator<V> iterator()
		{
			return newValueIterator();
		}

		public int size()
		{
			return size;
		}

		public boolean contains(Object o)
		{
			return containsValue(o);
		}

		public void clear()
		{
			HashMap.this.clear();
		}
	}

	/**
	 * Returns a {@link Set} view of the mappings contained in this map. The set is backed by the map, so changes to the
	 * map are reflected in the set, and vice-versa. If the map is modified while an iteration over the set is in
	 * progress (except through the iterator's own <tt>remove</tt> operation, or through the <tt>setValue</tt> operation
	 * on a map entry returned by the iterator) the results of the iteration are undefined. The set supports element
	 * removal, which removes the corresponding mapping from the map, via the <tt>Iterator.remove</tt>,
	 * <tt>Set.remove</tt>, <tt>removeAll</tt>, <tt>retainAll</tt> and <tt>clear</tt> operations. It does not support
	 * the <tt>add</tt> or <tt>addAll</tt> operations.
	 *
	 * @return a set view of the mappings contained in this map
	 */
	// 返回“HashMap的Entry集合”
	public Set<Map.Entry<K, V>> entrySet()
	{
		return entrySet0();
	}

	// 返回“HashMap的Entry集合”，它实际是返回一个EntrySet对象
	private Set<Map.Entry<K, V>> entrySet0()
	{
		Set<Map.Entry<K, V>> es = entrySet;
		return es != null ? es : (entrySet = new EntrySet());
	}

	// EntrySet对应的集合
	// EntrySet继承于AbstractSet，说明该集合中没有重复的EntrySet。
	private final class EntrySet extends AbstractSet<Map.Entry<K, V>>
	{
		public Iterator<Map.Entry<K, V>> iterator()
		{
			return newEntryIterator();
		}

		public boolean contains(Object o)
		{
			if (!(o instanceof Map.Entry))
				return false;
			Map.Entry<K, V> e = (Map.Entry<K, V>) o;
			Entry<K, V> candidate = getEntry(e.getKey());
			return candidate != null && candidate.equals(e);
		}

		public boolean remove(Object o)
		{
			return removeMapping(o) != null;
		}

		public int size()
		{
			return size;
		}

		public void clear()
		{
			HashMap.this.clear();
		}
	}

	/**
	 * Save the state of the <tt>HashMap</tt> instance to a stream (i.e., serialize it).
	 *
	 * @serialData The <i>capacity</i> of the HashMap (the length of the bucket array) is emitted (int), followed by the
	 *             <i>size</i> (an int, the number of key-value mappings), followed by the key (Object) and value
	 *             (Object) for each key-value mapping. The key-value mappings are emitted in no particular order.
	 */
	// java.io.Serializable的写入函数
	// 将HashMap的“总的容量，实际容量，所有的Entry”都写入到输出流中
	private void writeObject(java.io.ObjectOutputStream s) throws IOException
	{
		// Write out the threshold, loadfactor, and any hidden stuff
		s.defaultWriteObject();

		// Write out number of buckets
		if (table == EMPTY_TABLE)
		{
			s.writeInt(roundUpToPowerOf2(threshold));
		}
		else
		{
			s.writeInt(table.length);
		}

		// Write out size (number of Mappings)
		s.writeInt(size);

		// Write out keys and values (alternating)
		if (size > 0)
		{
			for (Map.Entry<K, V> e : entrySet0())
			{
				s.writeObject(e.getKey());
				s.writeObject(e.getValue());
			}
		}
	}

	private static final long serialVersionUID = 362498820763181265L;

	/**
	 * Reconstitute the {@code HashMap} instance from a stream (i.e., deserialize it).
	 */
	// java.io.Serializable的读取函数：根据写入方式读出
	// 将HashMap的“总的容量，实际容量，所有的Entry”依次读出
	private void readObject(java.io.ObjectInputStream s) throws IOException, ClassNotFoundException
	{
		// Read in the threshold (ignored), loadfactor, and any hidden stuff
		s.defaultReadObject();
		if (loadFactor <= 0 || Float.isNaN(loadFactor))
		{
			throw new InvalidObjectException("Illegal load factor: " + loadFactor);
		}

		// set other fields that need values
		table = (Entry<K, V>[]) EMPTY_TABLE;

		// Read in number of buckets
		s.readInt(); // ignored.

		// Read number of mappings
		int mappings = s.readInt();
		if (mappings < 0)
			throw new InvalidObjectException("Illegal mappings count: " + mappings);

		// capacity chosen by number of mappings and desired load (if >= 0.25)
		int capacity = (int) Math.min(mappings * Math.min(1 / loadFactor, 4.0f),
				// we have limits...
				HashMap.MAXIMUM_CAPACITY);

		// allocate the bucket array;
		if (mappings > 0)
		{
			inflateTable(capacity);
		}
		else
		{
			threshold = capacity;
		}

		init();  // Give subclass a chance to do its thing.

		// Read the keys and values, and put the mappings in the HashMap
		for (int i = 0; i < mappings; i++)
		{
			K key = (K) s.readObject();
			V value = (V) s.readObject();
			putForCreate(key, value);
		}
	}

	// These methods are used when serializing HashSets
	// 返回“HashMap总的容量”
	int capacity()
	{
		return table.length;
	}

	// 返回“HashMap的加载因子”
	float loadFactor()
	{
		return loadFactor;
	}
}
