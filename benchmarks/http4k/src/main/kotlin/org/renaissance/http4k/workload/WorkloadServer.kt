package org.renaissance.http4k.workload

import org.http4k.core.HttpHandler
import org.http4k.core.Method
import org.http4k.core.Response
import org.http4k.core.Status
import org.http4k.routing.bind
import org.http4k.routing.path
import org.http4k.routing.routes
import org.http4k.server.Http4kServer
import org.http4k.server.Undertow
import org.http4k.server.asServer
import org.renaissance.http4k.model.Product
import java.util.concurrent.ConcurrentHashMap

internal class WorkloadServer(port: Int) : Http4kServer {
    private val server = app().asServer(Undertow(port))
    private val products: MutableMap<String, Product> = ConcurrentHashMap<String, Product>()

    private fun app(): HttpHandler = routes(
        "/product" bind Method.GET to { Product.productsLens(products.values.toTypedArray(), Response(Status.OK)) },
        "/product/{id}" bind Method.GET to {
            when (val id = it.path("id")) {
                null -> Response(Status.BAD_REQUEST)
                !in products -> Response(Status.NOT_FOUND)
                else -> {
                    val product = products[id] ?: error("Invariant error: Product $it should be present")
                    Product.productLens(product, Response(Status.OK))
                }
            }
        },
        "/product" bind Method.POST to {
            val product = Product.productLens(it)
            products[product.id] = product
            Response(Status.CREATED)
        }
    )

    override fun port(): Int = server.port()

    override fun start(): Http4kServer {
        server.start()
        return this
    }

    override fun stop(): Http4kServer {
        server.stop()
        products.clear()
        return this
    }
}