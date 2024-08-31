package org.renaissance.http4k.workload

import kotlinx.coroutines.*
import org.http4k.core.HttpHandler
import org.http4k.core.Method
import org.http4k.core.Request
import org.renaissance.http4k.model.Product
import java.util.*
import java.util.concurrent.atomic.AtomicLong
import kotlin.random.Random

/**
 * Client used to generate workloads for the http4k server.
 * The client sends requests to the server based on the workload type.
 * @param client HttpHandler used to send requests to the server.
 * @param configuration WorkloadConfiguration used to generate the workload.
 */
internal class WorkloadClient(
    private val client: HttpHandler, private val configuration: WorkloadConfiguration
) {
    private val getProductsCounter = AtomicLong(0)
    private val getProductCounter = AtomicLong(0)
    private val postProductCounter = AtomicLong(0)

    private val readCounter = AtomicLong(0)
    private val writeCounter = AtomicLong(0)
    private val ddosCounter = AtomicLong(0)
    private val mixedCounter = AtomicLong(0)

    private val workloadCounter = AtomicLong(0)

    private val dispatcher = Dispatchers.IO.limitedParallelism(configuration.maxThreads, "Workload")

    /**
     * Starts the workload on the server based on [configuration].
     * Each workload consists of read, write, ddos and mixed requests.
     * The number of workloads is determined by [WorkloadConfiguration.workloadCount].
     * The number of requests for each workload type is determined by the corresponding configuration value.
     * Random workload is generated for each iteration based on the seed in [WorkloadConfiguration.workloadSelectorSeed].
     * @return WorkloadResult containing number of requests per type used for validation.
     */
    suspend fun workload(): WorkloadSummary = coroutineScope {
        val random = Random(configuration.workloadSelectorSeed)
        withContext(dispatcher) {
            range(configuration.workloadCount).flatMap {
                when (random.nextWorkload()) {
                    WorkloadType.READ -> range(configuration.readWorkloadRepeatCount).map { async { client.readWorkload() } }
                    WorkloadType.WRITE -> range(configuration.writeWorkloadRepeatCount).map { async { client.writeWorkload() } }
                    WorkloadType.DDOS -> range(configuration.ddosWorkloadRepeatCount).map { async { client.ddosWorkload() } }
                    WorkloadType.MIXED -> range(configuration.mixedWorkloadRepeatCount).map { async { client.mixedWorkload() } }
                }.also { workloadCounter.incrementAndGet() }
            }.awaitAll()

            WorkloadSummary(
                getProductsCount = getProductsCounter.get(),
                getProductCount = getProductCounter.get(),
                postProductCount = postProductCounter.get(),
                readCount = readCounter.get(),
                writeCount = writeCounter.get(),
                ddosCount = ddosCounter.get(),
                mixedCount = mixedCounter.get(),
                workloadCount = workloadCounter.get()
            )
        }
    }

    /**
     * Read workload gets all products and then iterates over each one and gets the specific product.
     */
    private fun HttpHandler.readWorkload() {
        val products = getProducts()
        products.forEach { product ->
            getProduct(product.id)
        }
        readCounter.incrementAndGet()
    }

    /**
     * Write workload creates a new product.
     */
    private fun HttpHandler.writeWorkload() {
        val product = generateProduct()
        postProduct(product)
        writeCounter.incrementAndGet()
    }

    /**
     * DDOS workload reads all products 10 times in a row.
     */
    private fun HttpHandler.ddosWorkload() {
        repeat(10) {
            getProducts()
        }
        ddosCounter.incrementAndGet()
    }

    /**
     * Mixed workload reads all products, then creates a new product and fetches it afterward.
     */
    private fun HttpHandler.mixedWorkload() {
        getProducts()
        val product = generateProduct()
        postProduct(product)
        getProduct(product.id)
        mixedCounter.incrementAndGet()
    }

    /**
     * Helper functions to interact with the server.
     */
    private fun HttpHandler.getProducts(): List<Product> =
        Product.productsLens(this(Request(Method.GET, configuration.url("product")))).toList()
            .also { getProductsCounter.incrementAndGet() }

    private fun HttpHandler.getProduct(id: String) =
        this(Request(Method.GET, configuration.url("product/$id"))).also { getProductCounter.incrementAndGet() }

    private fun HttpHandler.postProduct(product: Product) = this(
        Product.productLens(
            product,
            Request(Method.POST, configuration.url("product"))
        )
    ).also { postProductCounter.incrementAndGet() }

    /**
     * Helper function to generate a URL from the configuration.
     */
    private fun WorkloadConfiguration.url(endpoint: String) = "http://$host:$port/$endpoint"

    /**
     * Helper function to generate a random workload type.
     */
    private fun Random.nextWorkload() = WorkloadType.entries[nextInt(WorkloadType.entries.size)]

    /**
     * Helper function to generate a new product with random id.
     */
    private fun generateProduct(): Product {
        val id = UUID.randomUUID().toString()
        val name = "Product $id"
        return Product(id, name)
    }

    private fun range(end: Int) = (1..end)
}