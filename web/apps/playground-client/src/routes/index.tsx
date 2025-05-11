import { createFileRoute } from "@tanstack/react-router";

export const Route = createFileRoute("/")({
  component: IndexPage,
});

function IndexPage() {
  // For the MVP, AppLayout in __root.tsx provides the main UI.
  // This page component can be minimal or empty.
  return (
    <div className="p-2">
      {/* Content for index page, if any, would go here. */}
      {/* For MVP, this might be empty as App.tsx handles the full layout */}
    </div>
  );
}
