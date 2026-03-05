/* -*- Header -*-
 * Umbrella header: include this for the full SMTParser API.
 * Order: core -> ir -> context -> passes -> frontend -> model.
 * Each header is self-contained; this order is for clarity only.
 */
#pragma once

#include "smtparser/core/asserting.h"
#include "smtparser/core/kind.h"
#include "smtparser/core/options.h"
#include "smtparser/core/timing.h"
#include "smtparser/core/util.h"
#include "smtparser/ir/sort.h"
#include "smtparser/ir/number.h"
#include "smtparser/ir/value.h"
#include "smtparser/ir/interval.h"
#include "smtparser/ir/dag.h"
#include "smtparser/ir/node.h"
#include "smtparser/context/context.h"
#include "smtparser/passes/op_dispatcher.h"
#include "smtparser/passes/visitor.h"
#include "smtparser/passes/rewriter.h"
#include "smtparser/frontend/parser_context.h"
#include "smtparser/frontend/symbol_manager.h"
#include "smtparser/frontend/objective.h"
#include "smtparser/frontend/op_utils.h"
#include "smtparser/frontend/parser.h"
#include "smtparser/model/model.h"
