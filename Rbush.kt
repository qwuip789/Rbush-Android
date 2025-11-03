package foifcad.math

import kotlin.math.*

// ----- 基本数据结构 -----

data class BBox(
    var minX: Double = Double.POSITIVE_INFINITY,
    var minY: Double = Double.POSITIVE_INFINITY,
    var maxX: Double = Double.NEGATIVE_INFINITY,
    var maxY: Double = Double.NEGATIVE_INFINITY
) {
    fun set(other: BBox): BBox {
        minX = other.minX; minY = other.minY; maxX = other.maxX; maxY = other.maxY
        return this
    }

    fun extend(other: BBox): BBox {
        minX = min(minX, other.minX)
        minY = min(minY, other.minY)
        maxX = max(maxX, other.maxX)
        maxY = max(maxY, other.maxY)
        return this
    }

    fun area(): Double = (maxX - minX) * (maxY - minY)
    fun margin(): Double = (maxX - minX) + (maxY - minY)
    fun intersects(b: BBox): Boolean =
        b.minX <= maxX && b.minY <= maxY && b.maxX >= minX && b.maxY >= minY

    fun contains(b: BBox): Boolean =
        minX <= b.minX && minY <= b.minY && b.maxX <= maxX && b.maxY <= maxY
}

data class Node<T>(
    val children: MutableList<Any>, // 子节点(Node<T>)或叶子元素(T)
    var leaf: Boolean = true,
    var height: Int = 1,
    val bbox: BBox = BBox()
)

// ----- 工具：quickselect / multiSelect -----

private fun <T> swap(a: MutableList<T>, i: Int, j: Int) {
    val t = a[i]; a[i] = a[j]; a[j] = t
}

/** 原版 quickselect 的 Kotlin 版（按 compare 局部选择第 k 项，使得 [left-k] 最小） */
private fun <T> quickselect(
    arr: MutableList<T>,
    k: Int,
    left0: Int = 0,
    right0: Int = arr.lastIndex,
    compare: (T, T) -> Int
) {
    var left = left0
    var right = right0
    var kk = k

    while (right > left) {
        if (right - left > 600) {
            val n = (right - left + 1).toDouble()
            val m = (kk - left + 1).toDouble()
            val z = ln(n)
            val s = 0.5 * exp(2 * z / 3)
            val sd = 0.5 * sqrt(z * s * (n - s) / n) * if (m - n / 2 < 0) -1 else 1
            val newLeft = max(left, floor(kk - m * s / n + sd).toInt())
            val newRight = min(right, floor(kk + (n - m) * s / n + sd).toInt())
            quickselect(arr, kk, newLeft, newRight, compare)
        }

        val t = arr[kk]
        var i = left
        var j = right

        swap(arr, left, kk)
        if (compare(arr[right], t) > 0) swap(arr, left, right)

        while (i < j) {
            swap(arr, i, j)
            i++; j--
            while (compare(arr[i], t) < 0) i++
            while (compare(arr[j], t) > 0) j--
        }

        if (compare(arr[left], t) == 0) swap(arr, left, j)
        else {
            j++
            swap(arr, j, right)
        }

        if (j <= kk) left = j + 1
        if (kk <= j) right = j - 1
    }
}

/** 原版 multiSelect：将区间 [left,right] 分块，每块内部无序，但块间有序 */
private fun <T> multiSelect(
    arr: MutableList<T>,
    left0: Int,
    right0: Int,
    n: Int,
    compare: (T, T) -> Int
) {
    val stack = ArrayDeque<Int>()
    stack.addLast(left0); stack.addLast(right0)

    while (stack.isNotEmpty()) {
        var right = stack.removeLast()
        var left = stack.removeLast()

        if (right - left <= n) continue

        val mid = left + ceil((right - left).toDouble() / n / 2).toInt() * n
        quickselect(arr, mid, left, right, compare)

        stack.addLast(left); stack.addLast(mid)
        stack.addLast(mid); stack.addLast(right)
    }
}

// ----- RBush 主体 -----

/**
 * Kotlin 版 RBush（R-tree），等价于 https://github.com/mourner/rbush
 *
 * @param maxEntries 每个结点最多元素数（默认 9）
 * @param toBBox 将泛型 T 转为包围盒 BBox 的函数
 */
class RBush<T : Any>(
    maxEntries: Int = 9,
    private val toBBox: (T) -> BBox
) {

    private val _maxEntries: Int = max(4, maxEntries)
    private val _minEntries: Int = max(2, ceil(_maxEntries * 0.4).toInt())

    private var data: Node<T> = createNode(mutableListOf())

    fun clear(): RBush<T> {
        data = createNode(mutableListOf())
        return this
    }

    fun all(): List<T> = mutableListOf<T>().also { _all(data, it) }

    fun toJSON(): Node<T> = data.copy(
        children = data.children.toMutableList(),
        leaf = data.leaf,
        height = data.height,
        bbox = data.bbox.copy()
    )

    fun fromJSON(node: Node<T>): RBush<T> {
        data = node
        return this
    }

    fun insert(item: T): RBush<T> {
        _insert(item, data.height - 1, isNode = false)
        return this
    }

    fun load(items: List<T>): RBush<T> {
        if (items.isEmpty()) return this

        if (items.size < _minEntries) {
            for (it in items) insert(it)
            return this
        }

        var node = _build(items.toMutableList(), 0, items.lastIndex, 0)

        if (data.children.isEmpty()) {
            data = node
        } else if (data.height == node.height) {
            _splitRoot(data, node)
        } else {
            if (data.height < node.height) {
                val tmp = data
                data = node
                node = tmp
            }
            _insert(node, data.height - node.height - 1, isNode = true)
        }
        return this
    }

    /** 搜索与 bbox 相交的元素（二维区域检索） */
    fun search(bbox: BBox): List<T> {
        val result = mutableListOf<T>()
        var node: Node<T>? = data
        if (!bbox.intersects(node!!.bbox)) return result

        val nodesToSearch = ArrayDeque<Node<T>>()

        while (node != null) {
            val children = node.children
            if (node.leaf) {
                for (i in children.indices) {
                    @Suppress("UNCHECKED_CAST")
                    val item = children[i] as T
                    val childBBox = toBBox(item)
                    if (bbox.intersects(childBBox)) result.add(item)
                }
            } else {
                for (i in children.indices) {
                    @Suppress("UNCHECKED_CAST")
                    val childNode = children[i] as Node<T>
                    if (bbox.intersects(childNode.bbox)) {
                        if (bbox.contains(childNode.bbox)) _all(childNode, result)
                        else nodesToSearch.addLast(childNode)
                    }
                }
            }
            node = if (nodesToSearch.isEmpty()) null else nodesToSearch.removeLast()
        }
        return result
    }

    /** 是否存在与 bbox 相交的任何元素（更快的存在性判断） */
    fun collides(bbox: BBox): Boolean {
        var node: Node<T>? = data
        if (!bbox.intersects(node!!.bbox)) return false

        val nodesToSearch = ArrayDeque<Node<T>>()

        while (node != null) {
            val children = node.children
            if (node.leaf) {
                for (i in children.indices) {
                    @Suppress("UNCHECKED_CAST")
                    val item = children[i] as T
                    if (bbox.intersects(toBBox(item))) return true
                }
            } else {
                for (i in children.indices) {
                    @Suppress("UNCHECKED_CAST")
                    val childNode = children[i] as Node<T>
                    if (bbox.intersects(childNode.bbox)) {
                        if (bbox.contains(childNode.bbox)) return true
                        nodesToSearch.addLast(childNode)
                    }
                }
            }
            node = if (nodesToSearch.isEmpty()) null else nodesToSearch.removeLast()
        }
        return false
    }

    /** condense path: remove empty nodes, update BBoxes like JS version */
    private fun _condense(path: MutableList<Node<T>>) {
        var i = path.lastIndex

        while (i >= 0) {
            val node = path[i]

            if (node.children.isEmpty()) {

                // if not root, remove from parent
                if (i > 0) {
                    val parent = path[i - 1]
                    parent.children.remove(node)
                } else {
                    // root empty -> clear entire tree
                    clear()
                    return
                }

            } else {
                // update BBox
                calcBBox(node)
            }
            i--
        }
    }

    /** 从树中移除一个元素（需要 equals 判等；不传则使用 ==） */
    fun remove(item: T, equalsFn: ((T, T) -> Boolean)? = null): RBush<T> {
        val eq = equalsFn ?: { a: T, b: T -> a == b }

        var node: Node<T>? = data
        val bbox = toBBox(item)
        val path = ArrayList<Node<T>>()
        val indexes = ArrayList<Int>()
        var i = 0
        var parent: Node<T>? = null
        var goingUp = false

        while (node != null || path.isNotEmpty()) {
            if (node == null) {
                node = path.removeLast()
                parent = path.lastOrNull()
                i = indexes.removeLast()
                goingUp = true
            }

            if (node!!.leaf) {
                val idx = findItem(item, node.children, eq)
                if (idx != -1) {
                    node.children.removeAt(idx)
                    path.add(node)
                    _condense(path)
                    return this
                }
            }

            if (!goingUp && !node.leaf && node.bbox.contains(bbox)) {
                path.add(node)
                indexes.add(i)
                i = 0
                parent = node
                @Suppress("UNCHECKED_CAST")
                node = node.children[0] as Node<T>
            } else if (parent != null) {
                i++
                @Suppress("UNCHECKED_CAST")
                node = if (i < parent.children.size) parent.children[i] as Node<T> else null
                goingUp = false
            } else {
                node = null
            }
        }
        return this
    }

    // ----- 内部实现 -----

    private fun createNode(children: MutableList<Any>): Node<T> = Node(children, true, 1, BBox())

    private fun _all(node: Node<T>, result: MutableList<T>) {
        val stack = ArrayDeque<Node<T>>()
        var cur: Node<T>? = node
        while (cur != null) {
            if (cur.leaf) {
                for (o in cur.children) {
                    @Suppress("UNCHECKED_CAST")
                    result.add(o as T)
                }
            } else {
                for (o in cur.children) {
                    @Suppress("UNCHECKED_CAST")
                    stack.addLast(o as Node<T>)
                }
            }
            cur = if (stack.isEmpty()) null else stack.removeLast()
        }
    }

    private fun calcBBox(node: Node<T>) {
        val b = node.bbox
        b.minX = Double.POSITIVE_INFINITY
        b.minY = Double.POSITIVE_INFINITY
        b.maxX = Double.NEGATIVE_INFINITY
        b.maxY = Double.NEGATIVE_INFINITY

        if (node.leaf) {
            for (o in node.children) {
                @Suppress("UNCHECKED_CAST")
                b.extend(toBBox(o as T))
            }
        } else {
            for (o in node.children) {
                @Suppress("UNCHECKED_CAST")
                val n = o as Node<T>
                b.extend(n.bbox)
            }
        }
    }

    private fun distBBox(
        node: Node<T>, k: Int, p: Int, dest: BBox = BBox()
    ): BBox {
        dest.minX = Double.POSITIVE_INFINITY
        dest.minY = Double.POSITIVE_INFINITY
        dest.maxX = Double.NEGATIVE_INFINITY
        dest.maxY = Double.NEGATIVE_INFINITY

        if (node.leaf) {
            for (i in k until p) {
                @Suppress("UNCHECKED_CAST")
                dest.extend(toBBox(node.children[i] as T))
            }
        } else {
            for (i in k until p) {
                @Suppress("UNCHECKED_CAST")
                dest.extend((node.children[i] as Node<T>).bbox)
            }
        }
        return dest
    }

    private fun _build(items: MutableList<T>, left: Int, right: Int, height0: Int): Node<T> {
        val N = right - left + 1
        var M = _maxEntries
        var height = height0
        if (N <= M) {
            val children = items.subList(left, right + 1).map { it as Any }.toMutableList()
            val node = createNode(children)
            calcBBox(node)
            return node
        }
        if (height == 0) {
            height = ceil(ln(N.toDouble()) / ln(M.toDouble())).toInt()
            M = ceil(N / M.toDouble().pow((height - 1).toDouble())).toInt()
        }

        val node = createNode(mutableListOf())
        node.leaf = false
        node.height = height

        val N2 = ceil(N / M.toDouble()).toInt()
        val N1 = N2 * ceil(sqrt(M.toDouble())).toInt()

        // 按 minX 分块
        val tmp = items.subList(left, right + 1).toMutableList()
        tmp.sortWith { a, b -> toBBox(a).minX.compareTo(toBBox(b).minX) }
        val itemsRef = tmp

        fun sliceToMutable(startIncl: Int, endIncl: Int): MutableList<T> {
            val end = min(endIncl, itemsRef.lastIndex)
            return itemsRef.subList(startIncl, end + 1).toMutableList()
        }

        var i = 0
        while (i < N) {
            val right2 = min(i + N1 - 1, N - 1)
            val block = sliceToMutable(i, right2)
            // 每块内再按 minY 分块
            block.sortWith { a, b -> toBBox(a).minY.compareTo(toBBox(b).minY) }

            var j = 0
            while (j < block.size) {
                val right3 = min(j + N2 - 1, block.size - 1)
                val sub = block.subList(j, right3 + 1).toMutableList()
                val child = _build(sub, 0, sub.lastIndex, height - 1)
                node.children.add(child)
                j += N2
            }
            i += N1
        }

        calcBBox(node)
        return node
    }

    private fun _adjustParentBBoxes(bbox: BBox, path: List<Node<T>>, level: Int) {
        for (i in level downTo 0) path[i].bbox.extend(bbox)
    }

    private fun _chooseSubtree(
        bbox: BBox,
        node: Node<T>,
        level: Int,
        path: MutableList<Node<T>>
    ): Node<T> {
        var n = node
        while (true) {
            path.add(n)
            if (n.leaf || path.size - 1 == level) break

            var minArea = Double.POSITIVE_INFINITY
            var minEnlargement = Double.POSITIVE_INFINITY
            var target: Node<T>? = null

            for (o in n.children) {
                @Suppress("UNCHECKED_CAST")
                val child = o as Node<T>
                val area = child.bbox.area()
                val enlarged = enlargedArea(bbox, child.bbox) - area
                if (enlarged < minEnlargement) {
                    minEnlargement = enlarged
                    minArea = min(minArea, area)
                    target = child
                } else if (enlarged == minEnlargement && area < minArea) {
                    minArea = area
                    target = child
                }
            }
            n = target ?: (n.children[0] as Node<T>)
        }
        return n
    }

    private fun _insert(itemOrNode: Any, level: Int, isNode: Boolean) {
        val bbox = if (isNode) (itemOrNode as Node<T>).bbox else toBBox(itemOrNode as T)
        val insertPath = mutableListOf<Node<T>>()
        val node = _chooseSubtree(bbox, data, level, insertPath)

        node.children.add(itemOrNode)
        node.bbox.extend(bbox)

        var lvl = level
        while (lvl >= 0) {
            if ((insertPath[lvl].children.size) > _maxEntries) {
                _split(insertPath, lvl)
                lvl--
            } else break
        }
        _adjustParentBBoxes(bbox, insertPath, lvl)
    }

    private fun _split(insertPath: MutableList<Node<T>>, level: Int) {
        val node = insertPath[level]
        val M = node.children.size
        val m = _minEntries

        _chooseSplitAxis(node, m, M)
        val splitIndex = _chooseSplitIndex(node, m, M)

        val newChildren = node.children.subList(splitIndex, node.children.size).toMutableList()
        node.children.subList(splitIndex, node.children.size).clear()

        @Suppress("UNCHECKED_CAST")
        val newNode = Node<T>(
            children = newChildren,
            leaf = node.leaf,
            height = node.height,
            bbox = BBox()
        )

        calcBBox(node)
        calcBBox(newNode)

        if (level > 0) {
            insertPath[level - 1].children.add(newNode)
        } else {
            _splitRoot(node, newNode)
        }
    }

    private fun _splitRoot(node: Node<T>, newNode: Node<T>) {
        data = createNode(mutableListOf(node, newNode))
        data.leaf = false
        data.height = node.height + 1
        calcBBox(data)
    }

    private fun _chooseSplitIndex(node: Node<T>, m: Int, M: Int): Int {
        var index = 0
        var minOverlap = Double.POSITIVE_INFINITY
        var minArea = Double.POSITIVE_INFINITY

        for (i in m..(M - m)) {
            val bbox1 = distBBox(node, 0, i)
            val bbox2 = distBBox(node, i, M)
            val overlap = intersectionArea(bbox1, bbox2)
            val area = bbox1.area() + bbox2.area()

            if (overlap < minOverlap) {
                minOverlap = overlap
                index = i
                minArea = min(minArea, area)
            } else if (overlap == minOverlap && area < minArea) {
                minArea = area
                index = i
            }
        }
        return if (index == 0) M - m else index
    }

    private fun _chooseSplitAxis(node: Node<T>, m: Int, M: Int) {
        val xMargin = _allDistMargin(node, m, M) { a, b ->
            val (ba, bb) = _childBBox(node, a) to _childBBox(node, b)
            ba.minX.compareTo(bb.minX)
        }
        val yMargin = _allDistMargin(node, m, M) { a, b ->
            val (ba, bb) = _childBBox(node, a) to _childBBox(node, b)
            ba.minY.compareTo(bb.minY)
        }
        if (xMargin < yMargin) node.children.sortWith { a, b ->
            val (ba, bb) = _childBBox(node, a) to _childBBox(node, b)
            ba.minX.compareTo(bb.minX)
        } else {
            node.children.sortWith { a, b ->
                val (ba, bb) = _childBBox(node, a) to _childBBox(node, b)
                ba.minY.compareTo(bb.minY)
            }
        }
    }

    private fun _childBBox(parent: Node<T>, child: Any): BBox =
        if (parent.leaf) toBBox(child as T) else (child as Node<T>).bbox

    private fun _allDistMargin(node: Node<T>, m: Int, M: Int, cmp: (Any, Any) -> Int): Double {
        node.children.sortWith(cmp)

        val toBBox = { a: Any -> _childBBox(node, a) }
        val leftBBox = distBBox(node, 0, m)
        val rightBBox = distBBox(node, M - m, M)
        var margin = leftBBox.margin() + rightBBox.margin()

        run {
            val b = BBox().set(leftBBox)
            for (i in m until M - m) {
                b.extend(toBBox(node.children[i]))
                margin += b.margin()
            }
        }
        run {
            val b = BBox().set(rightBBox)
            for (i in M - m - 1 downTo m) {
                b.extend(toBBox(node.children[i]))
                margin += b.margin()
            }
        }
        return margin
    }

    private fun enlargedArea(a: BBox, b: BBox): Double {
        val minX = min(b.minX, a.minX)
        val minY = min(b.minY, a.minY)
        val maxX = max(b.maxX, a.maxX)
        val maxY = max(b.maxY, a.maxY)
        return (maxX - minX) * (maxY - minY)
    }

    private fun intersectionArea(a: BBox, b: BBox): Double {
        val minX = max(a.minX, b.minX)
        val minY = max(a.minY, b.minY)
        val maxX = min(a.maxX, b.maxX)
        val maxY = min(a.maxY, b.maxY)
        return max(0.0, maxX - minX) * max(0.0, maxY - minY)
    }

    private fun findItem(item: T, items: MutableList<Any>, eq: (T, T) -> Boolean): Int {
        for (i in items.indices) {
            @Suppress("UNCHECKED_CAST")
            val v = items[i] as? T ?: continue
            if (eq(item, v)) return i
        }
        return -1
    }
}
