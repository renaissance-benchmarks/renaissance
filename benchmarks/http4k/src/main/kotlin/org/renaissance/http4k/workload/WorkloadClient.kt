package org.renaissance.http4k.workload

import org.http4k.core.HttpHandler
import org.http4k.core.Method
import org.http4k.core.Request
import org.renaissance.http4k.model.Product
import java.util.*
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import kotlin.random.Random

/**
 * Client used to generate workloads for the http4k server.
 * The client sends requests to the server based on the workload type.
 * @param client HttpHandler used to send requests to the server.
 * @param configuration WorkloadConfiguration used to generate the workload.
 */
internal class WorkloadClient(
    private val client: HttpHandler,
    private val configuration: WorkloadConfiguration
) {
    private val random = Random(configuration.workloadSelectorSeed)
    private val executor = Executors.newFixedThreadPool(configuration.maxThreads)

    /**
     * Starts the workload on the server based on [configuration].
     * Each workload consists of read, write, ddos and mixed requests.
     * The number of workloads is determined by [WorkloadConfiguration.workloadCount].
     * The number of requests for each workload type is determined by the corresponding configuration value.
     * Random workload is generated for each iteration based on the seed in [WorkloadConfiguration.workloadSelectorSeed].
     */
    fun workload() {
        repeat(configuration.workloadCount) {
            when (randomWorkload()) {
                WorkloadType.READ -> repeat(configuration.readWorkloadRepeatCount) { client.readWorkload() }
                WorkloadType.WRITE -> repeat(configuration.writeWorkloadRepeatCount) { client.writeWorkload() }
                WorkloadType.DDOS -> repeat(configuration.ddosWorkloadRepeatCount) { client.ddosWorkload() }
                WorkloadType.MIXED -> repeat(configuration.mixedWorkloadRepeatCount) { client.mixedWorkload() }
            }
        }

        executor.shutdown()
        executor.awaitTermination(1, TimeUnit.MINUTES)
    }

    /**
     * Read workload gets all products and then iterates over each one and gets the specific product.
     */
    private fun HttpHandler.readWorkload() = executor.submit {
        val products = getProducts()
        products.forEach { product ->
            getProduct(product.id)
        }
    }

    /**
     * Write workload creates a new product.
     */
    private fun HttpHandler.writeWorkload() = executor.submit {
        val product = generateProduct()
        postProduct(product)
    }

    /**
     * DDOS workload reads all products 10 times in a row.
     */
    private fun HttpHandler.ddosWorkload() = repeat(10) {
        executor.submit {
            getProducts()
        }
    }

    /**
     * Mixed workload reads all products, then creates a new product and fetches it afterward.
     */
    private fun HttpHandler.mixedWorkload() = executor.submit {
        getProducts()
        val product = generateProduct()
        postProduct(product)
        getProduct(product.id)
    }

    /**
     * Helper functions to interact with the server.
     */
    private fun HttpHandler.getProducts() =
        Product.productsLens(this(Request(Method.GET, configuration.url("products"))))

    private fun HttpHandler.getProduct(id: String) =
        this(Request(Method.GET, configuration.url("products/$id")))

    private fun HttpHandler.postProduct(product: Product) =
        this(Product.productLens(product, Request(Method.POST, configuration.url("products"))))

    /**
     * Helper function to generate a URL from the configuration.
     */
    private fun WorkloadConfiguration.url(endpoint: String) = "https://$host:$port/$endpoint"

    /**
     * Helper function to generate a random workload type.
     */
    private fun randomWorkload() = WorkloadType.entries[random.nextInt(WorkloadType.entries.size)]

    /**
     * Helper function to generate a new product with random id.
     */
    private fun generateProduct(): Product {
        val id = UUID.randomUUID().toString()
        val name = "Product $id"
        return Product(id, name)
    }
}