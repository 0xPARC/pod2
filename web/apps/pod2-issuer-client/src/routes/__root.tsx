import { Outlet, createRootRoute } from "@tanstack/react-router";
import { TanStackRouterDevtools } from "@tanstack/react-router-devtools";
import { UserProvider } from "../contexts/UserContext";

export const Route = createRootRoute({
  component: () => (
    <UserProvider>
      <Outlet />
      <TanStackRouterDevtools />
    </UserProvider>
  ),
});
