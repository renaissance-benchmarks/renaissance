package org.renaissance.jdk.streams;


import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;


public class MnemonicsCoderWithStream {
  List<String> words; // Input dict words

  public void setDictWords(List<String> aWords) {
    words = aWords;
  }

  private Map<Character,String> mnemonics = new HashMap<>();

  {
    mnemonics.put('2',"ABC");
    mnemonics.put('3',"DEF");
    mnemonics.put('4',"GHI");
    mnemonics.put('5',"JKL");
    mnemonics.put('6',"MNO");
    mnemonics.put('7',"PQRS");
    mnemonics.put('8',"TUV");
    mnemonics.put('9',"WXYZ");
  }

  /** Invert the mnemonics map to give a map from chars 'A' ... 'Z' to '2' ... '9'
   * e.g. Map(E -> 3, X -> 9, N -> 6, T -> 8, Y -> 9,...)  */
  private Map<Character,Character> charCode = new HashMap<>(); {
    for(char ch = 'A'; ch <= 'Z'; ch++) {
      for(char getKey: mnemonics.keySet()) {
        if (mnemonics.get(getKey).contains(String.valueOf(ch))) {
          charCode.put(ch,getKey);
        }
      }
    }
  }

  /** Maps a word to the digit string it can represent, e.g. "Java" -> "5282" */
  private String wordCode(String word) {
    word = word.toUpperCase();
    String digit_str = "";
    for(int i = 0; i < word.length(); i++) {
      digit_str+=charCode.get(word.charAt(i));
    }
    return digit_str;
  }

  /** A map from digit strings to the words that represent them,
   *  e.g. "5282" -> Set("Java", "Kata", "Lava", ...) */
  private Map<String, List<String>> wordsForNum(List<String> dict_input, boolean parallel) {
    if (parallel) {
      return dict_input.stream().parallel().collect(Collectors.groupingBy(e -> wordCode(e)));
    } else {
      return dict_input.stream().collect(Collectors.groupingBy(e -> wordCode(e)));
    }
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
    return wordsForNum(words, false).entrySet().stream().filter(y -> number.endsWith(y.getKey()))
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
        wordsForNum(words, true).entrySet().stream();
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
