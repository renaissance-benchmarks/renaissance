package org.renaissance.actors

import org.renaissance.BenchmarkResult.ValidationException
import org.renaissance.actors.AkkaUct.Scenario
import org.renaissance.actors.AkkaUct.ScenarioResult
import org.scalatest.funsuite.AnyFunSuite

final class AkkaUctValidationTest extends AnyFunSuite {

  private val tolerance = 1e-5

  private val scenario: Scenario = {
    val topology = TestTopologies.generate(500, 5, 1)
    val urgentLeafIds = new UctUrgentPathSelector(4, 0.5).selectUrgentLeaves(topology)
    val shockTemperature = AkkaUct.computeShockTemperature(topology, urgentLeafIds, 1e-2)

    Scenario(
      ExpansionPlan.of(topology),
      AkkaUct.treeChecksum(topology),
      urgentLeafIds,
      shockTemperature,
      AkkaUct.nominalRootTemperature(topology),
      AkkaUct.shockedRootTemperature(topology, urgentLeafIds.toSet, shockTemperature)
    )
  }

  private val nominalTemperature = scenario.expectedNominalTemperature
  private val shockedTemperature = scenario.expectedShockedTemperature

  /** A result that meets every expectation of the scenario. */
  private val result = ScenarioResult(
    scenario.expectedTreeChecksum,
    scenario.expectedUrgentLeafIds,
    IndexedSeq(nominalTemperature, (nominalTemperature + shockedTemperature) / 2),
    shockedTemperature
  )

  //
  // Reversing the urgent leaves must change their order for the urgent leaf check to fail.
  //
  require(result.urgentLeafIds.size > 1)

  test("a result meeting the expectations passes every check") {
    val scenarios = Array(scenario)
    val results = Array(result)

    AkkaUct.validateNoUnexpectedMessages(Seq.empty)
    AkkaUct.validateTreeChecksums(scenarios, results)
    AkkaUct.validateUrgentLeaves(scenarios, results)
    AkkaUct.validateRacingTemperatureRanges(scenarios, results, tolerance)
    AkkaUct.validateRacingTemperatureOrder(scenarios, results, tolerance)
    AkkaUct.validateUrgentUpdateShown(scenarios, results, tolerance)
    AkkaUct.validateTemperaturesAfterUpdate(scenarios, results, tolerance)
  }

  test("an unexpected message fails the validation") {
    assertThrows[ValidationException] {
      AkkaUct.validateNoUnexpectedMessages(Seq(CreateSubtreeMessage))
    }
  }

  test("a tree checksum other than that of the topology fails the validation") {
    val checksum = result.treeChecksum.combinedWith(TreeChecksum.of(NodeId(1000)))
    val brokenResult = result.copy(treeChecksum = checksum)

    assertThrows[ValidationException] {
      AkkaUct.validateTreeChecksums(Array(scenario), Array(brokenResult))
    }
  }

  test("the expected urgent leaves in a different order fail the validation") {
    val brokenResult = result.copy(urgentLeafIds = result.urgentLeafIds.reverse)

    assertThrows[ValidationException] {
      AkkaUct.validateUrgentLeaves(Array(scenario), Array(brokenResult))
    }
  }

  test("a racing temperature below the nominal temperature fails the validation") {
    val temperatures = IndexedSeq(nominalTemperature - 10 * tolerance, shockedTemperature)
    val brokenResult = result.copy(racingRootTemperatures = temperatures)

    assertThrows[ValidationException] {
      AkkaUct.validateRacingTemperatureRanges(Array(scenario), Array(brokenResult), tolerance)
    }
  }

  test("a racing temperature above the shocked temperature fails the validation") {
    val temperatures = IndexedSeq(nominalTemperature, shockedTemperature + 10 * tolerance)
    val brokenResult = result.copy(racingRootTemperatures = temperatures)

    assertThrows[ValidationException] {
      AkkaUct.validateRacingTemperatureRanges(Array(scenario), Array(brokenResult), tolerance)
    }
  }

  test("a racing temperature lower than the one before fails the validation") {
    val temperatures = IndexedSeq(shockedTemperature, nominalTemperature)
    val brokenResult = result.copy(racingRootTemperatures = temperatures)

    assertThrows[ValidationException] {
      AkkaUct.validateRacingTemperatureOrder(Array(scenario), Array(brokenResult), tolerance)
    }
  }

  test("racing temperatures without the update fail the validation") {
    val temperatures = IndexedSeq.fill(3)(nominalTemperature)
    val brokenResult = result.copy(racingRootTemperatures = temperatures)

    assertThrows[ValidationException] {
      AkkaUct.validateUrgentUpdateShown(Array(scenario), Array(brokenResult), tolerance)
    }
  }

  test("a temperature after the update other than the shocked one fails the validation") {
    val temperature = (nominalTemperature + shockedTemperature) / 2
    val brokenResult = result.copy(rootTemperatureAfterUpdate = temperature)

    assertThrows[ValidationException] {
      AkkaUct.validateTemperaturesAfterUpdate(Array(scenario), Array(brokenResult), tolerance)
    }
  }

  test("racing temperatures with the update in one topology pass the validation") {
    val notShown = result.copy(racingRootTemperatures = IndexedSeq.fill(3)(nominalTemperature))

    AkkaUct.validateUrgentUpdateShown(
      Array(scenario, scenario),
      Array(notShown, result),
      tolerance
    )
  }

}
