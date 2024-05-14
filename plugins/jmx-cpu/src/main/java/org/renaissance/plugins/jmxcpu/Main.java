package org.renaissance.plugins.jmxcpu;

import java.lang.management.OperatingSystemMXBean;
import java.lang.management.ManagementFactory;

import org.renaissance.Plugin;

public class Main implements Plugin,
        Plugin.AfterOperationSetUpListener,
        Plugin.BeforeOperationTearDownListener,
        Plugin.MeasurementResultPublisher {

    OperatingSystemMXBean __operatingSystemMXBean;

    boolean __isPlatformSpecific;
    double __systemLoadAverageBefore;
    double __systemLoadAverageAfter;
    int __availableProcessorsBefore;
    int __availableProcessorsAfter;
    long __processCpuTimeBefore;
    long __processCpuTimeAfter;
    double __systemCpuLoadBefore;
    double __systemCpuLoadAfter;
    double __processCpuLoadAfter;
    double __processCpuLoadBefore;


    public Main() {
        __operatingSystemMXBean = ManagementFactory.getOperatingSystemMXBean();
        __isPlatformSpecific = __operatingSystemMXBean instanceof com.sun.management.OperatingSystemMXBean;
    }

    @Override
    public void afterOperationSetUp(String benchmark, int opIndex, boolean isLastOp) {
        if (__isPlatformSpecific) {
            __processCpuTimeBefore = ((com.sun.management.OperatingSystemMXBean)__operatingSystemMXBean).getProcessCpuTime();
            __systemCpuLoadBefore = ((com.sun.management.OperatingSystemMXBean)__operatingSystemMXBean).getSystemCpuLoad();
            __processCpuLoadBefore = ((com.sun.management.OperatingSystemMXBean)__operatingSystemMXBean).getProcessCpuLoad();
        }
        __systemLoadAverageBefore = __operatingSystemMXBean.getSystemLoadAverage();
        __availableProcessorsBefore = __operatingSystemMXBean.getAvailableProcessors();
    }

    @Override
    public void beforeOperationTearDown(String benchmark, int opIndex, long harnessDuration) {
        if (__isPlatformSpecific) {
            __processCpuTimeAfter = ((com.sun.management.OperatingSystemMXBean)__operatingSystemMXBean).getProcessCpuTime();
            __systemCpuLoadAfter = ((com.sun.management.OperatingSystemMXBean)__operatingSystemMXBean).getSystemCpuLoad();
            __processCpuLoadAfter = ((com.sun.management.OperatingSystemMXBean)__operatingSystemMXBean).getProcessCpuLoad();
        }
        __systemLoadAverageAfter = __operatingSystemMXBean.getSystemLoadAverage();
        __availableProcessorsAfter = __operatingSystemMXBean.getAvailableProcessors();
    }

    @Override
    public void onMeasurementResultsRequested(String benchmark, int opIndex, Plugin.MeasurementResultListener dispatcher){
        dispatcher.onMeasurementResult(benchmark, "jmx_cpu_load_average", (long)__systemLoadAverageAfter);
        dispatcher.onMeasurementResult(benchmark, "jmx_cpu_load_average_delta", (long)(__systemLoadAverageAfter - __systemLoadAverageBefore));
        dispatcher.onMeasurementResult(benchmark, "jmx_cpu_available_processors", __availableProcessorsAfter);
        dispatcher.onMeasurementResult(benchmark, "jmx_cpu_available_processors_delta", __availableProcessorsAfter - __availableProcessorsBefore);
        if (__isPlatformSpecific) {
            dispatcher.onMeasurementResult(benchmark, "jmx_cpu_process_cpu_time_ns", __processCpuTimeAfter);
            dispatcher.onMeasurementResult(benchmark, "jmx_cpu_process_cpu_time_delta_ns", __processCpuTimeAfter - __processCpuTimeBefore);
            dispatcher.onMeasurementResult(benchmark, "jmx_cpu_cpu_load", (long) (__systemCpuLoadAfter * 100));
            if (Double.isNaN(__systemCpuLoadAfter) || Double.isNaN(__systemCpuLoadBefore)) {
                dispatcher.onMeasurementResult(benchmark, "jmx_cpu_cpu_load_delta", 0);
            }
            else {
                dispatcher.onMeasurementResult(benchmark, "jmx_cpu_cpu_load_delta", (long)((__systemCpuLoadAfter - __systemCpuLoadBefore) * 100));
            }
            dispatcher.onMeasurementResult(benchmark, "jmx_cpu_process_load", (long) (__processCpuLoadAfter * 100));
            if (Double.isNaN(__processCpuLoadAfter) || Double.isNaN(__processCpuLoadBefore)) {
                dispatcher.onMeasurementResult(benchmark, "jmx_cpu_process_load_delta", 0);
            }
            else {
                dispatcher.onMeasurementResult(benchmark, "jmx_cpu_process_load_delta", (long)((__processCpuLoadAfter - __processCpuLoadBefore) * 100));
            }
        }
    }
}