package org.renaissance.http4k.model

import org.http4k.core.Body
import org.http4k.format.Moshi.auto

internal data class Product(val id: String, val name: String) {
    internal companion object {
        internal val productLens = Body.auto<Product>().toLens()
        internal val productsLens = Body.auto<Array<Product>>().toLens()
    }
}