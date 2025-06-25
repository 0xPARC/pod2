import { Outlet, createRootRoute } from "@tanstack/react-router";
import { TanStackRouterDevtools } from "@tanstack/react-router-devtools";
import AppLayout from "../App";

export const Route = createRootRoute({
  component: () => (
    <AppLayout>
      <Outlet />
      <TanStackRouterDevtools position="top-right" />
    </AppLayout>
  ),
});
