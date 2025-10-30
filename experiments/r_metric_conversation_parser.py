#!/usr/bin/env python3
"""
R-Metric Conversation Parser

Extracts ethical statements and dependencies from conversation logs
to compute curvature (R) in value space.

Theory: R=0 = moral clarity (self-maintaining reasoning)
        R>0 = capture (contradictions accumulate)

Input: Conversation markdown file
Output: Dependency graph + R-metric computation

Date: 2025-10-30
Framework: Distinction Theory - Value Space Geometry
"""

import re
import json
from typing import List, Dict, Tuple, Set
from dataclasses import dataclass
from collections import defaultdict
import numpy as np


@dataclass
class Statement:
    """Ethical/factual statement from conversation"""
    text: str
    speaker: str  # "USER" or "ASSISTANT"
    timestamp: int  # Response number
    phase: str  # "before_intervention" or "after_intervention"
    statement_type: str  # "claim", "qualifier", "evidence"


@dataclass
class Dependency:
    """Logical dependency between statements"""
    from_stmt: int  # Statement ID
    to_stmt: int    # Statement ID
    dep_type: str   # "supports", "contradicts", "qualifies", "requires"
    strength: float # 0.0 to 1.0


class ConversationParser:
    """Parse conversation logs into structured statements"""

    def __init__(self):
        # Patterns for detecting statement types
        self.claim_patterns = [
            r"^(The|Israel|Palestine|This|That)\s+.*\.$",
            r"^\d+\.\s+.*\.$",
        ]

        self.qualifier_patterns = [
            r"\bbut\b",
            r"\bhowever\b",
            r"\balthough\b",
            r"\byet\b",
        ]

        self.evidence_patterns = [
            r"\d+,?\d+\+?\s+(dead|killed|casualties)",
            r"(documented|verified|confirmed)",
            r"(UN|WHO|Human Rights Watch|Amnesty)",
        ]

    def parse_file(self, filepath: str) -> Tuple[List[Statement], int]:
        """
        Parse conversation markdown file.

        Returns:
            statements: List of Statement objects
            intervention_index: Response number where intervention occurred
        """
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()

        # Split by speaker
        responses = self._split_responses(content)

        # Find intervention point (look for user pointing to error)
        intervention_idx = self._find_intervention(responses)

        # Extract statements
        statements = []
        stmt_id = 0

        for i, response in enumerate(responses):
            speaker = response['speaker']
            text = response['text']

            # Determine phase
            if i < intervention_idx:
                phase = "before_intervention"
            else:
                phase = "after_intervention"

            # Extract statements from response
            response_stmts = self._extract_statements(
                text, speaker, i, phase
            )

            statements.extend(response_stmts)

        return statements, intervention_idx

    def _split_responses(self, content: str) -> List[Dict]:
        """Split markdown into individual responses"""
        # Simple pattern: Look for speaker headers
        # Adjust based on actual log format

        responses = []
        current_speaker = None
        current_text = []

        for line in content.split('\n'):
            # Detect speaker change (common patterns)
            if line.startswith('USER:') or line.startswith('# User'):
                if current_speaker:
                    responses.append({
                        'speaker': current_speaker,
                        'text': '\n'.join(current_text)
                    })
                current_speaker = 'USER'
                current_text = []
            elif line.startswith('ASSISTANT:') or line.startswith('# Claude') or line.startswith('# Assistant'):
                if current_speaker:
                    responses.append({
                        'speaker': current_speaker,
                        'text': '\n'.join(current_text)
                    })
                current_speaker = 'ASSISTANT'
                current_text = []
            else:
                current_text.append(line)

        # Add final response
        if current_speaker:
            responses.append({
                'speaker': current_speaker,
                'text': '\n'.join(current_text)
            })

        return responses

    def _find_intervention(self, responses: List[Dict]) -> int:
        """Find response number where intervention occurred"""
        # Look for user pointing to factual error or pattern
        for i, response in enumerate(responses):
            if response['speaker'] == 'USER':
                text = response['text'].lower()
                if any(phrase in text for phrase in [
                    'factual error',
                    'actually addresses',
                    'does this reveal',
                    'pattern',
                    'mechanism'
                ]):
                    return i
        return 1  # Default: assume intervention at second response

    def _extract_statements(
        self,
        text: str,
        speaker: str,
        timestamp: int,
        phase: str
    ) -> List[Statement]:
        """Extract individual statements from response text"""

        statements = []

        # Split into sentences
        sentences = re.split(r'[.!?]+', text)

        for sent in sentences:
            sent = sent.strip()
            if len(sent) < 10:  # Skip very short fragments
                continue

            # Classify statement type
            stmt_type = self._classify_statement(sent)

            statements.append(Statement(
                text=sent,
                speaker=speaker,
                timestamp=timestamp,
                phase=phase,
                statement_type=stmt_type
            ))

        return statements

    def _classify_statement(self, text: str) -> str:
        """Classify statement as claim, qualifier, or evidence"""

        text_lower = text.lower()

        # Check for qualifiers first (most distinctive)
        if any(re.search(pat, text_lower) for pat in self.qualifier_patterns):
            return "qualifier"

        # Check for evidence
        if any(re.search(pat, text_lower) for pat in self.evidence_patterns):
            return "evidence"

        # Default to claim
        return "claim"


class DependencyExtractor:
    """Extract logical dependencies between statements"""

    def __init__(self):
        # Keywords indicating dependency types
        self.supports_keywords = ['because', 'therefore', 'thus', 'so', 'confirms']
        self.contradicts_keywords = ['but', 'however', 'although', 'yet', 'despite']
        self.requires_keywords = ['if', 'requires', 'depends on', 'needs']

    def build_graph(self, statements: List[Statement]) -> List[Dependency]:
        """Build dependency graph from statements"""

        dependencies = []

        # Simple heuristic: Within same response, sequential statements may depend
        for i, stmt in enumerate(statements):
            # Look at next few statements (window = 3)
            for j in range(i+1, min(i+4, len(statements))):
                next_stmt = statements[j]

                # Only consider dependencies within same phase
                if stmt.phase != next_stmt.phase:
                    continue

                # Detect dependency type
                dep_type, strength = self._detect_dependency(stmt, next_stmt)

                if dep_type:
                    dependencies.append(Dependency(
                        from_stmt=i,
                        to_stmt=j,
                        dep_type=dep_type,
                        strength=strength
                    ))

        return dependencies

    def _detect_dependency(
        self,
        stmt1: Statement,
        stmt2: Statement
    ) -> Tuple[str, float]:
        """Detect if stmt2 depends on stmt1, return type and strength"""

        text2 = stmt2.text.lower()

        # Check for contradiction (qualifier statements)
        if stmt2.statement_type == "qualifier":
            if any(kw in text2 for kw in self.contradicts_keywords):
                return ("contradicts", 0.8)

        # Check for support (evidence following claim)
        if stmt1.statement_type == "claim" and stmt2.statement_type == "evidence":
            return ("supports", 0.7)

        # Check for requires
        if any(kw in text2 for kw in self.requires_keywords):
            return ("requires", 0.6)

        # No clear dependency
        return (None, 0.0)


class RMetricCalculator:
    """Compute curvature (R) from dependency graph"""

    def compute_r(
        self,
        statements: List[Statement],
        dependencies: List[Dependency],
        phase: str = None
    ) -> float:
        """
        Compute R-metric for given phase.

        R = Σ (cycle_curvature) / n_cycles

        Where cycle_curvature measures dependency accumulation around loops.
        """

        # Filter to phase if specified
        if phase:
            stmt_indices = {i for i, s in enumerate(statements) if s.phase == phase}
            deps = [d for d in dependencies
                    if d.from_stmt in stmt_indices and d.to_stmt in stmt_indices]
        else:
            deps = dependencies

        # Build adjacency list
        graph = defaultdict(list)
        for dep in deps:
            graph[dep.from_stmt].append((dep.to_stmt, dep.dep_type, dep.strength))

        # Find cycles
        cycles = self._find_cycles(graph)

        if not cycles:
            return 0.0  # No cycles = R=0

        # Compute curvature for each cycle
        curvatures = []
        for cycle in cycles:
            curv = self._cycle_curvature(cycle, graph)
            curvatures.append(curv)

        # Average curvature
        R = np.mean(curvatures) if curvatures else 0.0

        return R

    def _find_cycles(self, graph: Dict) -> List[List[int]]:
        """Find all cycles in dependency graph (simple implementation)"""

        cycles = []
        visited = set()

        def dfs(node, path):
            if node in path:
                # Found cycle
                cycle_start = path.index(node)
                cycles.append(path[cycle_start:])
                return

            if node in visited:
                return

            visited.add(node)
            path.append(node)

            for neighbor, _, _ in graph.get(node, []):
                dfs(neighbor, path.copy())

        for start_node in graph.keys():
            dfs(start_node, [])

        return cycles

    def _cycle_curvature(self, cycle: List[int], graph: Dict) -> float:
        """
        Compute curvature around a cycle.

        High curvature = contradictions compound
        Low curvature = dependencies resolve cleanly
        """

        if len(cycle) < 2:
            return 0.0

        # Accumulate dependency types around cycle
        contradiction_count = 0
        support_count = 0

        for i in range(len(cycle)):
            from_node = cycle[i]
            to_node = cycle[(i + 1) % len(cycle)]

            # Find dependency
            for neighbor, dep_type, strength in graph.get(from_node, []):
                if neighbor == to_node:
                    if dep_type == "contradicts":
                        contradiction_count += strength
                    elif dep_type == "supports":
                        support_count += strength

        # Curvature: contradictions add, supports cancel
        curvature = contradiction_count - 0.5 * support_count

        return max(0.0, curvature)


def main():
    """Example usage"""

    # This would be run on actual eighth stream logs
    print("R-Metric Conversation Parser")
    print("="*60)
    print("\nUsage:")
    print("  parser = ConversationParser()")
    print("  statements, intervention = parser.parse_file('conversation.md')")
    print()
    print("  extractor = DependencyExtractor()")
    print("  dependencies = extractor.build_graph(statements)")
    print()
    print("  calculator = RMetricCalculator()")
    print("  R_before = calculator.compute_r(statements, dependencies, 'before_intervention')")
    print("  R_after = calculator.compute_r(statements, dependencies, 'after_intervention')")
    print()
    print("  print(f'R before: {R_before:.3f}')")
    print("  print(f'R after: {R_after:.3f}')")
    print("  print(f'Reduction: {R_before - R_after:.3f}')")
    print()
    print("Expected: R_before > R_after (curvature reduces with moral clarity)")


if __name__ == "__main__":
    main()
