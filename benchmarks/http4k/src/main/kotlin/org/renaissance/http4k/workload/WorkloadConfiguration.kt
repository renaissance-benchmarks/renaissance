package org.renaissance.http4k.workload

internal data class WorkloadConfiguration(
    val host: String,
    val port: Int,
    val readWorkloadRepeatCount: Int,
    val writeWorkloadRepeatCount: Int,
    val ddosWorkloadRepeatCount: Int,
    val mixedWorkloadRepeatCount: Int,
    val workloadCount: Int,
    val maxThreads: Int,
    val workloadSelectionSeed: Long,
)