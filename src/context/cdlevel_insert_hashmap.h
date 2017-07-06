/*********************                                                        */
/*! \file cdlevel_insert_hashmap.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Context-dependent map class with support for insertions at
 ** arbitrary levels.
 **
 ** For each key, the class stores the corresponding level that it has been
 ** inserted at in a separate map. Additionally, the class stores the ids at
 ** each level. When inserting, an existing element is only replaced if the new
 ** element has a lower level. When popping the context, the class
removes all elements with a higher level than the new context level.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__CONTEXT__CDLEVEL_INSERT_HASHMAP_H
#define __CVC4__CONTEXT__CDLEVEL_INSERT_HASHMAP_H

#include <ext/hash_map>
#include <vector>

#include "context/context.h"

namespace CVC4 {
namespace context {

template <class V>
struct deleteValue {
  void operator()(V& value) const {}
};

template <class K, class V, class DeleteValue = deleteValue<V> >
class CDLevelInsertHashMap : ContextNotifyObj {
 private:
  Context* d_context;
  __gnu_cxx::hash_map<K, V> d_keyValueMap;
  __gnu_cxx::hash_map<K, int> d_idLevelMap;
  std::vector<std::vector<K> > d_levelIdsMap;
  DeleteValue d_deleteValue;

 public:
  typedef typename __gnu_cxx::hash_map<K, V>::const_iterator const_iterator;
  typedef typename __gnu_cxx::hash_map<K, V>::iterator iterator;

  CDLevelInsertHashMap(Context* context)
      : ContextNotifyObj(context),
        d_context(context),
        d_keyValueMap(),
        d_levelIdsMap(),
        d_deleteValue() {}

  virtual void contextNotifyPop() {
    int newLevel = d_context->getLevel();
    for (int i = newLevel + 1; i < d_levelIdsMap.size(); i++) {
      const std::vector<K>& keysToRemove = d_levelIdsMap[i];
      for (int j = 0; j < keysToRemove.size(); j++) {
        const K& keyToRemove = keysToRemove[j];
        d_deleteValue(d_keyValueMap[keyToRemove]);
        d_keyValueMap.erase(keyToRemove);
        d_idLevelMap.erase(keyToRemove);
      }
    }
    d_levelIdsMap.resize(newLevel + 1);
  }

  /**
   * Insert a key-value pair at a given level. If the key already exists,
   * the value is only updated if the level is lower than the level of the
   * existing key-value pair.
   */
  void insert(K key, V value, int level) {
    if (d_idLevelMap.find(key) != d_idLevelMap.end() &&
        d_idLevelMap[key] <= level) {
      // If there is a value for the same key at a lower level, ignore the
      // insert
      return;
    }
    d_keyValueMap.insert(std::make_pair(key, value));
    d_idLevelMap.insert(std::make_pair(key, level));
    if (d_levelIdsMap.size() <= level) {
      d_levelIdsMap.resize(level + 1);
    }
    d_levelIdsMap[level].push_back(key);
  }

  const_iterator find(K key) const { return d_keyValueMap.find(key); }

  iterator find(K key) { return d_keyValueMap.find(key); }

  const_iterator begin() const { return d_keyValueMap.begin(); }

  iterator begin() { return d_keyValueMap.begin(); }

  const_iterator end() const { return d_keyValueMap.end(); }

  iterator end() { return d_keyValueMap.end(); }
};

} /* CVC4::context namespace */
} /* CVC4 namespace */

#endif /* __CVC4__CONTEXT__CDLEVEL_INSERT_HASHMAP_H */
