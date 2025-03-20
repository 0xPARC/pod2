import { describe, it, expect } from "vitest";
import { ValueSchema } from "./core-types";

describe("ValueSchema", () => {
  describe("primitive values", () => {
    it("should validate strings", () => {
      expect(ValueSchema.parse("hello")).toBe("hello");
    });

    it("should validate booleans", () => {
      expect(ValueSchema.parse(true)).toBe(true);
      expect(ValueSchema.parse(false)).toBe(false);
    });
  });

  describe("Int values", () => {
    it("should validate Int objects", () => {
      expect(ValueSchema.parse({ Int: "123" })).toEqual({ Int: "123" });
    });
  });

  describe("Raw values", () => {
    it("should validate Raw objects with correct format", () => {
      const validRaw = "0".repeat(64);
      expect(ValueSchema.parse({ Raw: validRaw })).toEqual({ Raw: validRaw });
    });

    it("should reject Raw objects with incorrect format", () => {
      expect(() => ValueSchema.parse({ Raw: "invalid" })).toThrow();
    });
  });

  describe("Set values", () => {
    it("should validate empty Sets", () => {
      expect(ValueSchema.parse({ Set: [] })).toEqual({ Set: [] });
    });

    it("should validate Sets with primitive values", () => {
      expect(ValueSchema.parse({ Set: ["hello"] })).toEqual({ Set: ["hello"] });
      expect(ValueSchema.parse({ Set: [true] })).toEqual({ Set: [true] });
    });

    it("should validate Sets with complex values", () => {
      expect(ValueSchema.parse({ Set: [{ Int: "123" }] })).toEqual({
        Set: [{ Int: "123" }]
      });
    });
  });

  describe("Dictionary values", () => {
    it("should validate empty Dictionaries", () => {
      expect(ValueSchema.parse({ Dictionary: {} })).toEqual({ Dictionary: {} });
    });

    it("should validate Dictionaries with primitive values", () => {
      expect(
        ValueSchema.parse({
          Dictionary: { key: "value" }
        })
      ).toEqual({
        Dictionary: { key: "value" }
      });
    });

    it("should validate Dictionaries with complex values", () => {
      expect(
        ValueSchema.parse({
          Dictionary: { key: { Int: "123" } }
        })
      ).toEqual({
        Dictionary: { key: { Int: "123" } }
      });
    });
  });

  describe("Array values", () => {
    it("should validate empty arrays", () => {
      expect(ValueSchema.parse([])).toEqual([]);
    });

    it("should validate arrays with primitive values", () => {
      expect(ValueSchema.parse(["hello", true])).toEqual(["hello", true]);
    });

    it("should validate arrays with complex values", () => {
      expect(
        ValueSchema.parse([{ Int: "123" }, { Raw: "0".repeat(64) }])
      ).toEqual([{ Int: "123" }, { Raw: "0".repeat(64) }]);
    });
  });
});
