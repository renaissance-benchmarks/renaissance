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
package org.renaissance.rx;



import io.reactivex.rxjava3.core.Maybe;
import io.reactivex.rxjava3.core.Observable;
import io.reactivex.rxjava3.core.Single;
import io.reactivex.rxjava3.functions.Function;
import io.reactivex.rxjava3.schedulers.Schedulers;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;
import java.util.TreeSet;



public class RxScrabbleImplementation extends Scrabble {
  public RxScrabbleImplementation(String scrabblePath, String shakespearePath) {
    super(scrabblePath, shakespearePath);
  }

  public List<Entry<Integer, List<String>>> runScrabble() throws Throwable {
    // Function to compute the score of a given word
    Function<Integer, Single<Integer>> scoreOfALetter =
      letter -> Single.just(letterScores[letter - 'a']);

    // score of the same letters in a word
    Function<Entry<Integer, LongWrapper>, Single<Integer>> letterScore =
      entry ->
        Single.just(
          letterScores[entry.getKey() - 'a'] *
            Integer.min(
              (int) entry.getValue().get(),
              scrabbleAvailableLetters[entry.getKey() - 'a']
            )
        );

    Function<String, Observable<Integer>> toIntegerObservable =
      string -> Observable.fromIterable(() -> string.chars().boxed().iterator());

    // Histogram of the letters in a given word
    Function<String, Single<HashMap<Integer, LongWrapper>>> histoOfLetters =
      word -> toIntegerObservable.apply(word)
        .collect(
          HashMap::new,
          (HashMap<Integer, LongWrapper> map, Integer value) ->
            map.merge(value, () -> 0L, (prev, cur) -> prev.inc())
        );

    // number of blanks for a given letter
    Function<Entry<Integer, LongWrapper>, Single<Long>> blank =
      entry ->
        Single.just(
          Long.max(
            0L,
            entry.getValue().get() -
              scrabbleAvailableLetters[entry.getKey() - 'a']
          )
        );

    // number of blanks for a given word
    Function<String, Maybe<Long>> nBlanks =
      word -> histoOfLetters.apply(word)
        .flattenAsObservable(Map::entrySet)
        .flatMapSingle(blank)
        .reduce(Long::sum);


    // can a word be written with 2 blanks?
    Function<String, Maybe<Boolean>> checkBlanks =
      word -> nBlanks.apply(word)
        .flatMap(l -> Maybe.just(l <= 2L));

    // score taking blanks into account letterScore1
    Function<String, Maybe<Integer>> score2 =
      word -> histoOfLetters.apply(word)
        .flattenAsObservable(Map::entrySet)
        .flatMapSingle(letterScore)
        .reduce(Integer::sum);

    // Placing the word on the board
    // Building the streams of first and last letters
    Function<String, Observable<Integer>> first3 =
      word -> Observable.fromIterable(() -> word.chars().limit(3).boxed().iterator());
    Function<String, Observable<Integer>> last3 =
      word -> Observable.fromIterable(() -> word.chars().skip(3).boxed().iterator());


    // Stream to be maxed
    Function<String, Observable<Integer>> toBeMaxed =
      word -> Observable.concat(first3.apply(word), last3.apply(word));

    // Bonus for double letter
    Function<String, Maybe<Integer>> bonusForDoubleLetter =
      word -> toBeMaxed.apply(word)
        .flatMapSingle(scoreOfALetter)
        .reduce(Integer::max);

    // score of the word put on the board
    Function<String, Maybe<Integer>> score3 =
      word ->
        Maybe.concatArray(
          score2.apply(word),
          score2.apply(word),
          bonusForDoubleLetter.apply(word),
          bonusForDoubleLetter.apply(word),
          Maybe.just(word.length() == 7 ? 50 : 0)
        )
        .reduce(Integer::sum);

    Function<
      Function<String, Maybe<Integer>>, Single<TreeMap<Integer, List<String>>>
      > buildHistoOnScore =
      score -> Observable.fromIterable(shakespeareWords)
        .buffer(1024)
        .flatMap(buffer ->
          Observable.fromIterable(buffer)
            .subscribeOn(Schedulers.computation())
            .filter(scrabbleWords::contains)
            .filter(word -> checkBlanks.apply(word).blockingGet())
        )
        .collect(
          () -> new TreeMap<>(Comparator.reverseOrder()),
          (TreeMap<Integer, List<String>> map, String word) -> {
            Integer key = score.apply(word).blockingGet();
            List<String> list = map.computeIfAbsent(key, k -> new ArrayList<>());
            list.add(word);
          });

    // best key / value pairs
    List<Entry<Integer, List<String>>> finalList2 =
      buildHistoOnScore.apply(score3)
        .flattenAsObservable(Map::entrySet)
        .collect(
          () -> new ArrayList<Entry<Integer, List<String>>>(),
          ArrayList::add
        )
        .blockingGet();

    return finalList2;
  }

  public static List<String> prepareForValidation(List<Entry<Integer, List<String>>> allWords) {
    List<String> result = new ArrayList<>(allWords.size());
    for (Entry<Integer, List<String>> entry : allWords) {
      Integer score = entry.getKey();
      String words = String.join("-", sortedUniqueWords(entry.getValue()));
      result.add(String.format("%d--%s", score, words));
    }
    return result;
  }

  private static List<String> sortedUniqueWords(List<String> words) {
    return new ArrayList<>(new TreeSet<>(words));
  }

}
