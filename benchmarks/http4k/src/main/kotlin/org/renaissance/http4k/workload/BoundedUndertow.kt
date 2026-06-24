package org.renaissance.http4k.workload

import io.undertow.Undertow
import io.undertow.server.handlers.BlockingHandler
import org.http4k.core.HttpHandler
import org.http4k.server.Http4kServer
import org.http4k.server.Http4kUndertowHttpHandler
import org.http4k.server.ServerConfig
import org.http4k.server.ServerConfig.StopMode
import org.http4k.server.ServerConfig.StopMode.Immediate
import java.net.InetSocketAddress

/**
 * Custom Undertow server configuration with a bounded number of worker threads.
 *
 * The default http4k [org.http4k.server.Undertow] uses 32 * availableProcessors()
 * worker threads, which prevents the server from becoming CPU-bound on large machines.
 * This wrapper allows controlling the worker thread count for more predictable
 * benchmark behavior.
 *
 * @param port Server port (0 for auto-allocation).
 * @param workerThreads Number of Undertow worker threads.
 */
internal class BoundedUndertow(
    private val port: Int = 0,
    private val workerThreads: Int = Runtime.getRuntime().availableProcessors()
) : ServerConfig {
    override val stopMode: StopMode = Immediate

    override fun toServer(http: HttpHandler): Http4kServer {
        val httpHandler = Http4kUndertowHttpHandler(http).let(::BlockingHandler)

        return object : Http4kServer {
            val server: Undertow = Undertow.builder()
                .addHttpListener(port, "0.0.0.0")
                .setWorkerThreads(workerThreads)
                .setHandler(httpHandler)
                .build()

            override fun start() = apply { server.start() }
            override fun stop() = apply { server.stop() }

            override fun port(): Int = when {
                port > 0 -> port
                else -> (server.listenerInfo[0].address as InetSocketAddress).port
            }
        }
    }
}
