package org.renaissance.jdk.streams;


import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;


public final class MnemonicsCoderWithStream {
  private List<String> words; // Input dict words

  public MnemonicsCoderWithStream(List<String> aWords) {
    words = aWords;
  }

  private final Map<Character, String> mnemonics = new HashMap<Character, String>() {{
    put('2',"ABC");
    put('3',"DEF");
    put('4',"GHI");
    put('5',"JKL");
    put('6',"MNO");
    put('7',"PQRS");
    put('8',"TUV");
    put('9',"WXYZ");
  }};

  /** Invert the mnemonics map to give a map from chars 'A' ... 'Z' to '2' ... '9'
   * e.g. Map(E -> 3, X -> 9, N -> 6, T -> 8, Y -> 9,...)  */
  private Map<Character, String> charCode = mnemonics.entrySet().stream()
          .flatMap(e -> e.getValue().chars().mapToObj(c -> (char) c)
                  .collect(Collectors.toMap(c -> c, c -> String.valueOf (e.getKey()))).entrySet().stream()
          ).collect (Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));

  /** Maps a word to the digit string it can represent, e.g. "Java" -> "5282" */
  private String wordCode(String word) {
    return word.chars()
            .mapToObj(c -> charCode.get (Character.toUpperCase((char) c)))
            .collect (Collectors.joining());
  }

  /** A map from digit strings to the words that represent them,
   *  e.g. "5282" -> Set("Java", "Kata", "Lava", ...) */
  private Map<String, List<String>> wordsForNum(List<String> words) {
    return words.stream().collect(Collectors.groupingBy(this::wordCode));
  }

  /** Same as above but in parallel */
  private Map<String, List<String>> wordsForNumParallel(List<String> words) {
    return words.stream().parallel().collect(Collectors.groupingByConcurrent(this::wordCode));
  }

  /** Return all ways to encode a number as a list of words
   *  Here, input a digit string that need to be encoded and
   *  a set of word phrases that have been translated in previous recursion.
   *  Return a set of word phrases, including the previous translated set and the word
   *  mapped from the digit number in this round.
   */
  Set<String> encode(String number, Set<String> currentResult) {
    /** If a digit string maps to two dict words, should return all possible words,
     *  e.g. ['222':['abc','adc'] ]
     */
    return wordsForNum(words).entrySet().stream().filter(y -> number.endsWith(y.getKey()))
        .flatMap(x -> x.getValue().stream())
        .map(x -> {
          /** Calls the encode() function recursively to encode the rest part of stream */
          Set<String> intermediate_res =
              encode(number.substring(0, (number.length() - x.length())),
                  currentResult.stream().map(y -> x + y).collect(Collectors.toSet()));
          if (x.length() == number.length())  return new HashSet<String>(Arrays.asList(x));
          /** Return the word phrase with a blank between two dict words
           *  e.g. "Scala rocks" */
          else  return intermediate_res.stream().map(y -> y + " " + x).collect(Collectors.toSet());
        })
        .flatMap(x -> x.stream())
        .collect(Collectors.toSet());
  }

  /** Maps a number to a list of all word phrases that can represent it. */
  public Set<String> translate(String number) {
    return encode(number, new HashSet<String>());
  }

  /** Return all ways to encode a number in parallel. */
  public Set<String> parallelEncode(String number, Set<String> currentResult) {
    /** If a digit string maps to two dict words, should return all possible words,
     *  e.g. ['222':['abc','adc'] ]
     */
    Stream<Map.Entry<String, List<String>>> baseWordStream =
            wordsForNumParallel(words).entrySet().stream();
    Stream<Map.Entry<String, List<String>>> wordStream =
        number.length() >= 3 ? baseWordStream.parallel() : baseWordStream;
    return wordStream
        .filter(y -> number.endsWith(y.getKey()))
        .flatMap(x -> x.getValue().stream())
        .map(x -> {
          /** Calls the encode() function recursively to encode the rest part of stream */
          Set<String> intermediate_res =
              encode(number.substring(0, (number.length() - x.length())),
                  currentResult.stream().map(y -> x + y).collect(Collectors.toSet()));
          if (x.length() == number.length()) {
            return new HashSet<String>(Arrays.asList(x));
          } else {
            return intermediate_res.stream().map(y -> y + " " + x).collect(Collectors.toSet());
          }
        })
        .flatMap(x -> x.stream())
        .collect(Collectors.toSet());
  }

  /** Maps a number to a list of all word phrases in parallel. */
  public Set<String> parallelTranslate(String number) {
    return parallelEncode(number, new HashSet<String>());
  }
}
