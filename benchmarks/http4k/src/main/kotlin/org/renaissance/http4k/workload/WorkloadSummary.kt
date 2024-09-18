package org.renaissance.http4k.workload

internal data class WorkloadSummary(
    val getProductsCount: Long,
    val getProductCount: Long,
    val postProductCount: Long,
    val readCount: Long,
    val writeCount: Long,
    val ddosCount: Long,
    val mixedCount: Long,
    val workloadCount: Long
)