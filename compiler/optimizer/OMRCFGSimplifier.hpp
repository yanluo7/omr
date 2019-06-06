/*******************************************************************************
 * Copyright (c) 2000, 2019 IBM Corp. and others
 *
 * This program and the accompanying materials are made available under
 * the terms of the Eclipse Public License 2.0 which accompanies this
 * distribution and is available at http://eclipse.org/legal/epl-2.0
 * or the Apache License, Version 2.0 which accompanies this distribution
 * and is available at https://www.apache.org/licenses/LICENSE-2.0.
 *
 * This Source Code may also be made available under the following Secondary
 * Licenses when the conditions for such availability set forth in the
 * Eclipse Public License, v. 2.0 are satisfied: GNU General Public License,
 * version 2 with the GNU Classpath Exception [1] and GNU General Public
 * License, version 2 with the OpenJDK Assembly Exception [2].
 *
 * [1] https://www.gnu.org/software/classpath/license.html
 * [2] http://openjdk.java.net/legal/assembly-exception.html
 *
 * SPDX-License-Identifier: EPL-2.0 OR Apache-2.0 OR GPL-2.0 WITH Classpath-exception-2.0 OR LicenseRef-GPL-2.0 WITH Assembly-exception
 *******************************************************************************/

#ifndef OMR_CFGSIMPLIFIER_INCL
#define OMR_CFGSIMPLIFIER_INCL

#include <stdint.h>
#include "optimizer/Optimization.hpp"
#include "optimizer/OptimizationManager.hpp"

namespace TR { class Block; }
namespace TR { class CFG; }
namespace TR { class CFGEdge; }
namespace TR { class Node; }
namespace TR { class TreeTop; }
template <class T> class ListElement;

namespace OMR
{

// Control flow graph simplifier
//
// Look for opportunities to simplify control flow.
//
class CFGSimplifier : public TR::Optimization
   {
   public:
   CFGSimplifier(TR::OptimizationManager *manager);
   static TR::Optimization *create(TR::OptimizationManager *manager)
      {
      return new (manager->allocator()) CFGSimplifier(manager);
      }

   virtual int32_t perform();
   virtual const char * optDetailString() const throw();
   
   protected:

   virtual bool simplifyIfPatterns(bool needToDuplicateTree);
   bool simplifyBooleanStore(bool needToDuplicateTree);
   bool simplifyNullToException(bool needToDuplicateTree);
   bool simplifySimpleStore(bool needToDuplicateTree);
   bool simplifyCondStoreSequence(bool needToDuplicateTree);
   bool simplifyInstanceOfTestToCheckcast(bool needToDuplicateTree);
   TR::TreeTop *getNextRealTreetop(TR::TreeTop *treeTop);
   TR::TreeTop *getLastRealTreetop(TR::Block *block);
   TR::Block   *getFallThroughBlock(TR::Block *block);
   bool hasExceptionPoint(TR::Block *block, TR::TreeTop *end);

   TR::CFG                  *_cfg;

   // Current block
   TR::Block                *_block;

   // First successor to the current block
   TR::CFGEdge              *_succ1;
   TR::Block                *_next1;

   // Second successor to the current block
   TR::CFGEdge              *_succ2;
   TR::Block                *_next2;

   private :

   bool simplify();
   bool simplifyIfStructure();
   bool simplifyCondCodeBooleanStore(TR::Block *joinBlock, TR::Node *branchNode, TR::Node *store1Node, TR::Node *store2Node);
   bool canReverseBranchMask();

   };

}

#endif
