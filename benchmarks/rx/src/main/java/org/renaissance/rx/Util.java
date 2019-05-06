package org.renaissance.rx;


import org.apache.commons.io.IOUtils;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;


public final class Util {
  private Util() {
  }

  public static Set<String> readScrabbleWords(String scrabblePath) {
    Set<String> scrabbleWords = new HashSet<>();
    Iterator<String> lines;
    try {
      lines = IOUtils.lineIterator(
        Util.class.getResourceAsStream(scrabblePath), StandardCharsets.UTF_8);
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
    Stream<String> scrabbleWordsStream = StreamSupport.stream(
      Spliterators.spliteratorUnknownSize(lines, Spliterator.ORDERED), false);
    scrabbleWords.addAll(
      scrabbleWordsStream.map(String::toLowerCase).collect(Collectors.toSet()));
    return scrabbleWords;
  }

  public static Set<String> readShakespeareWords(String shakespearePath) {
    Set<String> shakespeareWords = new HashSet<>();
    Iterator<String> lines;
    try {
      lines = IOUtils.lineIterator(
        Util.class.getResourceAsStream(shakespearePath), StandardCharsets.UTF_8);
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
    Stream<String> shakespeareWordsStream = StreamSupport.stream(
      Spliterators.spliteratorUnknownSize(lines, Spliterator.ORDERED), false);
    shakespeareWords.addAll(shakespeareWordsStream
      .flatMap(line -> Arrays.stream(line.split("\\s")))
      .map(String::toLowerCase).collect(Collectors.toSet())
    );
    return shakespeareWords;
  }
}
