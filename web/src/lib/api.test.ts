import { describe, it, expect } from "vitest";
import { formatValue } from "./core-types";

describe("Value Type Conversions", () => {
  describe("formatValue", () => {
    it("should format strings", () => {
      expect(formatValue("hello")).toBe('"hello"');
    });

    it("should format integers", () => {
      expect(formatValue({ Int: "123" })).toBe("123");
    });

    it("should format negative integers", () => {
      expect(formatValue({ Int: "-123" })).toBe("-123");
    });

    it("should format booleans", () => {
      expect(formatValue(true)).toBe("true");
    });

    it("should format arrays", () => {
      expect(formatValue(["hello", { Int: "123" }, true])).toBe(
        '["hello", 123, true]'
      );
    });

    it("should format dictionaries", () => {
      expect(
        formatValue({
          Dictionary: {
            str: "hello",
            num: { Int: "123" },
            bool: true
          }
        })
      ).toBe('{str: "hello", num: 123, bool: true}');
    });

    it("should format raw values", () => {
      expect(formatValue({ Raw: "1234567890abcdef" })).toBe(
        "Raw(1234567890abcdef)"
      );
    });
  });
});
