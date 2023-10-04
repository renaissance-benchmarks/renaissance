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



import rx.Observable;
import rx.Single;
import rx.functions.Func1;
import rx.schedulers.Schedulers;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map.Entry;
import java.util.TreeMap;
import java.util.TreeSet;



public class RxScrabbleImplementation extends Scrabble {
  public RxScrabbleImplementation(String scrabblePath, String shakespearePath) {
    super(scrabblePath, shakespearePath);
  }

  public List<Entry<Integer, List<String>>> runScrabble() throws InterruptedException {
    // Function to compute the score of a given word
    Func1<Integer, Single<Integer>> scoreOfALetter =
      letter -> Single.just(letterScores[letter - 'a']);

    // score of the same letters in a word
    Func1<Entry<Integer, LongWrapper>, Single<Integer>> letterScore =
      entry ->
        Single.just(
          letterScores[entry.getKey() - 'a'] *
            Integer.min(
              (int) entry.getValue().get(),
              scrabbleAvailableLetters[entry.getKey() - 'a']
            )
        );

    Func1<String, Observable<Integer>> toIntegerObservable =
      string -> Observable.from(() -> string.chars().boxed().iterator());

    // Histogram of the letters in a given word
    Func1<String, Single<HashMap<Integer, LongWrapper>>> histoOfLetters =
      word -> toIntegerObservable.call(word)
        .collect(
          HashMap::new,
          (HashMap<Integer, LongWrapper> map, Integer value) ->
            map.merge(value, () -> 0L, (prev, cur) -> prev.inc())
        ).toSingle();

    // number of blanks for a given letter
    Func1<Entry<Integer, LongWrapper>, Single<Long>> blank =
      entry ->
        Single.just(
          Long.max(
            0L,
            entry.getValue().get() -
              scrabbleAvailableLetters[entry.getKey() - 'a']
          )
        );

    // number of blanks for a given word
    Func1<String, Single<Long>> nBlanks =
      word -> histoOfLetters.call(word)
        .flatMapObservable(map -> Observable.from(map.entrySet()))
        .flatMapSingle(blank)
        .reduce(Long::sum).toSingle();


    // can a word be written with 2 blanks?
    Func1<String, Single<Boolean>> checkBlanks =
      word -> nBlanks.call(word)
        .flatMap(l -> Single.just(l <= 2L));

    // score taking blanks into account letterScore1
    Func1<String, Single<Integer>> score2 =
      word -> histoOfLetters.call(word)
        .flatMapObservable(map -> Observable.from(map.entrySet()))
        .flatMapSingle(letterScore)
        .reduce(Integer::sum).toSingle();

    // Placing the word on the board
    // Building the streams of first and last letters
    Func1<String, Observable<Integer>> first3 =
      word -> Observable.from(() -> word.chars().limit(3).boxed().iterator());
    Func1<String, Observable<Integer>> last3 =
      word -> Observable.from(() -> word.chars().skip(3).boxed().iterator());


    // Stream to be maxed
    Func1<String, Observable<Integer>> toBeMaxed =
      word -> Observable.concat(first3.call(word), last3.call(word));

    // Bonus for double letter
    Func1<String, Single<Integer>> bonusForDoubleLetter =
      word -> toBeMaxed.call(word)
        .flatMapSingle(scoreOfALetter)
        .reduce(Integer::max).toSingle();

    // score of the word put on the board
    Func1<String, Single<Integer>> score3 =
      word ->
        Single.concat(
          score2.call(word),
          score2.call(word),
          bonusForDoubleLetter.call(word),
          bonusForDoubleLetter.call(word),
          Single.just(word.length() == 7 ? 50 : 0)
        )
        .reduce(Integer::sum).toSingle();

    Func1<
      Func1<String, Single<Integer>>, Single<TreeMap<Integer, List<String>>>
      > buildHistoOnScore =
      score -> Observable.from(shakespeareWords)
        .buffer(1024)
        .flatMap(buffer ->
          Observable.from(buffer)
            .subscribeOn(Schedulers.computation())
            .filter(scrabbleWords::contains)
            .filter(word -> checkBlanks.call(word).toBlocking().value())
        )
        .collect(
          () -> new TreeMap<>(Comparator.reverseOrder()),
          (TreeMap<Integer, List<String>> map, String word) -> {
            Integer key = score.call(word).toBlocking().value();
            List<String> list = map.computeIfAbsent(key, k -> new ArrayList<>());
            list.add(word);
          }).toSingle();

    // best key / value pairs
    List<Entry<Integer, List<String>>> finalList2 =
      buildHistoOnScore.call(score3)
        .flatMapObservable(map -> Observable.from(map.entrySet()))
        .collect(
          () -> new ArrayList<Entry<Integer, List<String>>>(),
          ArrayList::add
        )
        .toBlocking()
        .first();

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
