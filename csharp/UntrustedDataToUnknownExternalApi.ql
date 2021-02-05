/**
 * @name Untrusted data passed to an unknown external API
 * @description Data provided remotely is used in this external API without sanitization, which could be a security risk.
 * @id csharp/untrusted-data-to-unknown-external-api
 * @kind path-problem
 * @precision low
 * @problem.severity error
 * @tags security external/cwe/cwe-20
 */

import csharp
import semmle.code.csharp.dataflow.TaintTracking
import semmle.code.csharp.security.dataflow.ExternalAPIs
import semmle.code.csharp.security.dataflow.flowsinks.Email
import semmle.code.csharp.security.dataflow.flowsinks.ExternalLocationSink
import semmle.code.csharp.security.dataflow.flowsinks.Html
import semmle.code.csharp.security.dataflow.flowsinks.Remote
import DataFlow::PathGraph

predicate isACommonSink(DataFlow::Node n) {
  n instanceof Email::Sink or
  n instanceof ExternalLocationSink or
  n instanceof HtmlSink or
  n instanceof RemoteFlowSink
}

class DotNetApi extends SafeExternalAPICallable {
  DotNetApi() { this.getDeclaringType().getNamespace().getParentNamespace*().getName() = "System" }
}

class ExternalUnknownAPIDataNode extends ExternalAPIDataNode {
  ExternalUnknownAPIDataNode() {
    // Not already modeled as a taint step
    not exists(DataFlow::Node next | TaintTracking::localTaintStep(this, next)) and
    not isACommonSink(this)
  }
}

/** A configuration for tracking flow from `RemoteFlowSource`s to `ExternalAPIDataNode`s. */
class UntrustedDataToUnknownExternalAPIConfig extends TaintTracking::Configuration {
  UntrustedDataToUnknownExternalAPIConfig() { this = "UntrustedDataToExternalAPIConfig" }

  override predicate isSource(DataFlow::Node source) { source instanceof RemoteFlowSource }

  override predicate isSink(DataFlow::Node sink) { sink instanceof ExternalUnknownAPIDataNode }
}

from UntrustedDataToExternalAPIConfig config, DataFlow::PathNode source, DataFlow::PathNode sink
where config.hasFlowPath(source, sink)
select sink, source, sink,
  "Call to " + sink.getNode().(ExternalUnknownAPIDataNode).getCallableDescription() +
    " with untrusted data from $@.", source, source.toString()
