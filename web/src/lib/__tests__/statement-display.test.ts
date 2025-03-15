import { describe, it, expect } from "vitest";
import {
  formatValue,
  formatAnchoredKey,
  formatArg,
  formatStatement,
  validateStatement,
  validateStatements
} from "../statement-display";
import { Statement, StatementArg, Value } from "../statement-display";

describe("statement display", () => {
  describe("formatValue", () => {
    it("formats string values", () => {
      const value: Value = { type: "String", value: "hello" };
      expect(formatValue(value)).toBe('"hello"');
    });

    it("formats integer values", () => {
      const value: Value = { type: "Int", value: 42 };
      expect(formatValue(value)).toBe("42");
    });

    it("formats boolean values", () => {
      const value: Value = { type: "Bool", value: true };
      expect(formatValue(value)).toBe("true");
    });

    it("formats raw values", () => {
      const value: Value = {
        type: "Raw",
        value:
          "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
      };
      expect(formatValue(value)).toBe(
        "Raw(0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef)"
      );
    });

    it("formats array values", () => {
      const value: Value = {
        type: "Array",
        value: [
          { type: "String", value: "hello" },
          { type: "Int", value: 42 }
        ]
      };
      expect(formatValue(value)).toBe('["hello", 42]');
    });

    it("formats set values", () => {
      const value: Value = {
        type: "Set",
        value: [
          { type: "String", value: "hello" },
          { type: "Int", value: 42 }
        ]
      };
      expect(formatValue(value)).toBe('Set("hello", 42)');
    });

    it("formats dictionary values", () => {
      const value: Value = {
        type: "Dictionary",
        value: {
          a: { type: "String", value: "hello" },
          b: { type: "Int", value: 42 }
        }
      };
      expect(formatValue(value)).toBe('{a: "hello", b: 42}');
    });
  });

  describe("formatAnchoredKey", () => {
    it("formats anchored keys", () => {
      const key = {
        origin: {
          pod_class: "Signed" as const,
          pod_id:
            "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
        },
        key: "test_key"
      };
      expect(formatAnchoredKey(key)).toBe(
        "Signed(0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef).test_key"
      );
    });
  });

  describe("formatArg", () => {
    it("formats key arguments", () => {
      const arg: StatementArg = {
        type: "Key",
        value: {
          origin: {
            pod_class: "Signed",
            pod_id:
              "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
          },
          key: "test_key"
        }
      };
      expect(formatArg(arg)).toBe(
        "Signed(0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef).test_key"
      );
    });

    it("formats literal arguments", () => {
      const arg: StatementArg = {
        type: "Literal",
        value: { type: "String", value: "hello" }
      };
      expect(formatArg(arg)).toBe('"hello"');
    });
  });

  describe("formatStatement", () => {
    it("formats native predicate statements", () => {
      const statement: Statement = {
        predicate: {
          type: "Native",
          value: "Equal"
        },
        args: [
          {
            type: "Key",
            value: {
              origin: {
                pod_class: "Signed",
                pod_id:
                  "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
              },
              key: "key1"
            }
          },
          {
            type: "Literal",
            value: { type: "String", value: "hello" }
          }
        ]
      };
      expect(formatStatement(statement)).toBe(
        'Equal(Signed(0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef).key1, "hello")'
      );
    });

    it("formats batch self statements", () => {
      const statement: Statement = {
        predicate: {
          type: "BatchSelf",
          value: 42
        },
        args: [
          {
            type: "Key",
            value: {
              origin: {
                pod_class: "Signed",
                pod_id:
                  "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
              },
              key: "key1"
            }
          }
        ]
      };
      expect(formatStatement(statement)).toBe(
        "BatchSelf(42)(Signed(0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef).key1)"
      );
    });

    it("formats custom predicate statements", () => {
      const statement: Statement = {
        predicate: {
          type: "Custom",
          value: [
            {
              name: "MyPredicate",
              predicates: [
                {
                  conjunction: true,
                  statements: [],
                  args_len: 2
                }
              ]
            },
            0
          ]
        },
        args: [
          {
            type: "Key",
            value: {
              origin: {
                pod_class: "Signed",
                pod_id:
                  "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
              },
              key: "key1"
            }
          }
        ]
      };
      expect(formatStatement(statement)).toBe(
        "MyPredicate[0](Signed(0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef).key1)"
      );
    });
  });

  describe("validation", () => {
    it("validates valid statements", () => {
      const statement: Statement = {
        predicate: {
          type: "Native",
          value: "Equal"
        },
        args: [
          {
            type: "Key",
            value: {
              origin: {
                pod_class: "Signed",
                pod_id:
                  "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
              },
              key: "key1"
            }
          },
          {
            type: "Literal",
            value: { type: "String", value: "hello" }
          }
        ]
      };
      expect(() => validateStatement(statement)).not.toThrow();
    });

    it("validates arrays of statements", () => {
      const statements: Statement[] = [
        {
          predicate: {
            type: "Native",
            value: "Equal"
          },
          args: [
            {
              type: "Key",
              value: {
                origin: {
                  pod_class: "Signed",
                  pod_id:
                    "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
                },
                key: "key1"
              }
            },
            {
              type: "Literal",
              value: { type: "String", value: "hello" }
            }
          ]
        }
      ];
      expect(() => validateStatements(statements)).not.toThrow();
    });

    it("rejects invalid statements", () => {
      const invalidStatement = {
        predicate: {
          type: "Invalid",
          value: "Equal"
        },
        args: []
      };
      expect(() => validateStatement(invalidStatement)).toThrow();
    });
  });
});
