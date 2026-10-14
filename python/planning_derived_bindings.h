// Independent registration: invoke after SomtPythonHir::bind(m).
#pragma once
#include "hir_bindings.h"
#include "somtparser/uir/planning_derived.h"

namespace SomtPythonPlanningDerived {
void bind(pybind11::module_& module);

} // namespace SomtPythonPlanningDerived
