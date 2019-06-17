/*
 * Copyright (C) 2014 Jose Paumard
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */
package org.renaissance.jdk.streams;


import org.apache.commons.io.IOUtils;
import org.renaissance.ValidationException;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.function.IntUnaryOperator;
import java.util.function.Predicate;
import java.util.function.ToIntFunction;
import java.util.function.ToLongFunction;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;


public class JavaScrabble {
  public static final int[] letterScores = {
    1, 3, 3, 2, 1, 4, 2, 4, 1, 8, 5, 1, 3, 1, 1, 3, 10, 1, 1, 1, 1, 4, 4, 8, 4, 10
  };

  public static final int[] scrabbleAvailableLetters = {
    9, 2, 2, 1, 12, 2, 3, 2, 9, 1, 1, 4, 2, 6, 8, 2, 1, 6, 4, 6, 4, 2, 2, 1, 2, 1
  };

  public static String[] allWords;

  public static Set<String> scrabbleWords;

  public JavaScrabble(String shakespearePath, String scrabblePath) throws RuntimeException {
    try {
      byte[] shakespeareBytes =
        IOUtils.toByteArray(JavaScrabble.class.getResourceAsStream(shakespearePath));
      allWords = new String(shakespeareBytes).split("\\s+");

      byte[] scrabbleBytes =
        IOUtils.toByteArray(JavaScrabble.class.getResourceAsStream(scrabblePath));
      String[] scrabbleWordArray = new String(scrabbleBytes).split("\\s+");
      scrabbleWords = new HashSet<>(Arrays.asList(scrabbleWordArray));
    } catch (Exception e) {
      throw new RuntimeException(e);
    }
  }

  public List<Entry<Integer, List<String>>> run() {
    // Function to compute the score of a given word
    IntUnaryOperator scoreOfALetter = letter -> letterScores[letter - 'A'];

    // score of the same letters in a word
    ToIntFunction<Entry<Integer, Long>> letterScore =
      entry ->
        letterScores[entry.getKey() - 'A'] *
          Integer.min(
            entry.getValue().intValue(),
            scrabbleAvailableLetters[entry.getKey() - 'A']
          );

    // Histogram of the letters in a given word
    Function<String, Map<Integer, Long>> histOfLetters =
      word -> word.chars().boxed()
        .collect(
          Collectors.groupingBy(
            Function.identity(),
            Collectors.counting()
          )
        );

    // number of blanks for a given letter
    ToLongFunction<Entry<Integer, Long>> blank =
      entry -> {
        return Long.max(
          0L,
          entry.getValue() -
            scrabbleAvailableLetters[entry.getKey() - 'A']
        );
      };

    // number of blanks for a given word
    Function<String, Long> nBlanks =
      word -> histOfLetters.apply(word)
        .entrySet().stream()
        .mapToLong(blank)
        .sum();

    // can a word be written with 2 blanks?
    Predicate<String> checkBlanks = word -> nBlanks.apply(word) <= 2;

    // score taking blanks into account
    Function<String, Integer> score2 =
      word -> histOfLetters.apply(word)
        .entrySet().stream()
        .mapToInt(letterScore)
        .sum();

    // Placing the word on the board
    // Building the streams of first and last letters
    Function<String, IntStream> first3 = word -> word.chars().limit(3);
    Function<String, IntStream> last3 = word -> word.chars().skip(Integer.max(0, word.length() - 4));

    // Stream to be maxed
    Function<String, IntStream> toBeMaxed =
      word -> Stream.of(first3.apply(word), last3.apply(word))
        .flatMapToInt(Function.identity());

    // Bonus for double letter
    ToIntFunction<String> bonusForDoubleLetter =
      word -> toBeMaxed.apply(word)
        .map(scoreOfALetter)
        .max()
        .orElse(0);

    // score of the word put on the board
    Function<String, Integer> score3 =
      word ->
        2 * (score2.apply(word) + bonusForDoubleLetter.applyAsInt(word))
          + (word.length() == 7 ? 50 : 0);

    Function<Function<String, Integer>, Map<Integer, List<String>>> buildHistoOnScore =
      score -> shakespeareWordStream()
        .filter(scrabbleWords::contains)
        .filter(checkBlanks) // filter out the words that needs more than 2 blanks
        .collect(
          Collectors.groupingBy(
            score,
            () -> new TreeMap<Integer, List<String>>(Comparator.reverseOrder()),
            Collectors.toList()
          )
        );

    // best key / value pairs
    List<Entry<Integer, List<String>>> finalList =
      buildHistoOnScore.apply(score3).entrySet()
        .stream()
        .limit(3)
        .collect(Collectors.toList());

    return finalList;
  }

  private final static Pattern nonAlphabetRegex = Pattern.compile(".*[^A-Z].*");

  private static boolean isAlphabetical(String word) {
    return !nonAlphabetRegex.matcher(word).find();
  }

  public static Stream<String> shakespeareWordStream() {
    return Arrays.stream(allWords)
      .parallel()
      .map(word -> {
        return word.toUpperCase();
      })
      .filter(word -> isAlphabetical(word));
  }
  
  public static List<String> prepareForValidation(List<Entry<Integer, List<String>>> bestWords) {
    List<String> result = new ArrayList<>(bestWords.size());
    for (Entry<Integer, List<String>> entry : bestWords) {
        Integer score = entry.getKey();
        String words = String.join("-", sortedUniqueWords(entry.getValue()));
        result.add(String.format("%d--%s", score, words));
    }
    return result;
  }
  
  private static List<String> sortedUniqueWords(List<String> words) {
    return new ArrayList<String>(new TreeSet<String>(words));
  }
  
  public static void validate(List<Entry<Integer, List<String>>> bestWords) {
    ValidationException.throwIfNotEqual(3, bestWords.size(), "list length");

    ValidationException.throwIfNotEqual(120, (int) bestWords.get(0).getKey(), "score of best word");
    ValidationException.throwIfNotEqual("QUICKLY", String.join("-", sortedUniqueWords(bestWords.get(0).getValue())), "best scoring word");

    ValidationException.throwIfNotEqual(118, (int) bestWords.get(1).getKey(), "score of second best word");
    ValidationException.throwIfNotEqual("ZEPHYRS", String.join("-", sortedUniqueWords(bestWords.get(1).getValue())), "second best scoring word");

    ValidationException.throwIfNotEqual(114, (int) bestWords.get(2).getKey(), "score of third best words");
    ValidationException.throwIfNotEqual("QUALIFY-QUICKEN-QUICKER", String.join("-", sortedUniqueWords(bestWords.get(2).getValue())), "third best scoring words");
  }
}
